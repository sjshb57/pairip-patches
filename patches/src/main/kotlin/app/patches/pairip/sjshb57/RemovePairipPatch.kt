package app.patches.pairip.sjshb57

import app.morphe.patcher.extensions.InstructionExtensions.addInstructions
import app.morphe.patcher.extensions.InstructionExtensions.instructions
import app.morphe.patcher.extensions.InstructionExtensions.instructionsOrNull
import app.morphe.patcher.extensions.InstructionExtensions.removeInstructions
import app.morphe.patcher.extensions.InstructionExtensions.replaceInstruction
import app.morphe.patcher.patch.BytecodePatchContext
import app.morphe.patcher.patch.bytecodePatch
import com.android.tools.smali.dexlib2.Opcode
import com.android.tools.smali.dexlib2.iface.instruction.OneRegisterInstruction
import com.android.tools.smali.dexlib2.iface.instruction.ReferenceInstruction
import com.android.tools.smali.dexlib2.iface.reference.FieldReference
import com.android.tools.smali.dexlib2.iface.reference.StringReference
import java.util.logging.Logger

/*
 * pairip 还原 patch（Morphe / 纯字节码，无 extension、无联网）
 *
 * 把原 pairip-restore 工具里"应用内自足"的几步移植到 Morphe Patcher：
 *   Step 1  收集字符串映射（情形 A：Application 类；情形 B：appkiller/ObjectLogger 风格）
 *   Step 2  把使用方的 sget-object 还原成 const-string
 *   Step 3  把所有调用 VMRunner 的方法体清空成最小返回
 *   Step 4  真正删除 com/pairip/ 类与字符串占位类（反射操作内部 classMap）
 *
 * 不做的事（按你的要求）：
 *   - 不删 synthetic 桩方法
 *   - 不做"真正方法体还原"（那需要联网下载库，已舍弃）
 */

private val logger = Logger.getLogger("RemovePairip")

private const val PAIRIP_PREFIX = "Lcom/pairip/"
private const val APPLICATION_CLASS = "Lcom/pairip/application/Application;"
private const val VMRUNNER_CLASS = "Lcom/pairip/VMRunner;"
private const val APPKILLER_METHOD = "appkiller"
private const val OBJECTLOGGER_SIG = "/ObjectLogger;->logstring("

/** 把真实字符串重新转义成 smali 字面量（dexlib2 给的是已解码字符串，写回 smali 必须重新转义） */
private fun String.toSmaliLiteral(): String = buildString {
    for (c in this@toSmaliLiteral) when (c) {
        '\\' -> append("\\\\")
        '"' -> append("\\\"")
        '\n' -> append("\\n")
        '\r' -> append("\\r")
        '\t' -> append("\\t")
        else -> append(c)
    }
}

/** 根据返回类型生成最小返回方法体（对应原 patcher.py 的 _default_return_body） */
private fun minimalReturnFor(returnType: String): String = when (returnType) {
    "V" -> "return-void"
    "Z", "B", "C", "S", "I", "F" -> "const/4 v0, 0x0\nreturn v0"
    "J", "D" -> "const-wide/16 v0, 0x0\nreturn-wide v0"
    else -> "const/4 v0, 0x0\nreturn-object v0" // 对象 / 数组 → null
}

/**
 * 通过反射拿到 BytecodePatchContext 内部的 classMap，用来真正删除类。
 * Morphe 没有公开删除类的 API；classMap 是 PatchClasses 的 internal 字段。
 * 风险：若 Morphe 内部字段重命名，这里会在运行时抛 NoSuchFieldException。
 */
@Suppress("UNCHECKED_CAST")
private fun BytecodePatchContext.internalClassMap(): MutableMap<String, *> {
    val patchClasses = BytecodePatchContext::class.java
        .getDeclaredField("patchClasses")
        .apply { isAccessible = true }
        .get(this)
    return patchClasses.javaClass
        .getDeclaredField("classMap")
        .apply { isAccessible = true }
        .get(patchClasses) as MutableMap<String, *>
}

@Suppress("unused")
val removePairipPatch = bytecodePatch(
    name = "Remove pairip protection",
    description = "Restores obfuscated strings and removes pairip bytecode protection.",
    default = true,
) {
    // 不声明 compatibleWith，按通用 patch 处理（可应用于任意被 pairip 加固的 app）

    execute {
        // fieldRef（形如 "Lx/Y;->z:Ljava/lang/String;"）-> 字符串值
        val stringMap = HashMap<String, String>()
        // 需要删除的字符串占位类（含 Application 类自身）
        val placeholderClasses = HashSet<String>()

        // ──────────────────────────────────────────────
        // Step 1A：从 com/pairip/application/Application 提取
        //          const-string vN, "value"  紧跟  sput-object vN, FIELD
        // ──────────────────────────────────────────────
        classDefForEach { classDef ->
            if (classDef.type != APPLICATION_CLASS) return@classDefForEach

            classDef.methods.forEach methods@{ method ->
                val insns = method.instructionsOrNull?.toList() ?: return@methods
                for (i in 0 until insns.size - 1) {
                    val cur = insns[i]
                    val next = insns[i + 1]
                    if (cur.opcode != Opcode.CONST_STRING) continue
                    if (next.opcode != Opcode.SPUT_OBJECT) continue

                    val value = ((cur as ReferenceInstruction).reference as StringReference).string
                    val fieldRef = (next as ReferenceInstruction).reference.toString()
                    stringMap[fieldRef] = value
                    placeholderClasses += fieldRef.substringBefore("->")
                }
            }
            placeholderClasses += APPLICATION_CLASS
        }

        // ──────────────────────────────────────────────
        // Step 1B：情形 A 没拿到任何配对时，扫 appkiller / ObjectLogger 风格
        //          在这些方法体里，模式是  sget-object FIELD  …  const-string "VALUE"
        //          （FIELD 在前、VALUE 在后，中间可夹杂其它指令 → 用状态机宽松配对）
        // ──────────────────────────────────────────────
        if (stringMap.isEmpty()) {
            classDefForEach { classDef ->
                val relevantMethods = classDef.methods.filter { method ->
                    val insns = method.instructionsOrNull ?: return@filter false
                    val isAppkiller = method.name == APPKILLER_METHOD &&
                        method.returnType == "V" &&
                        method.parameterTypes.isEmpty()
                    val hasLogger = insns.any { insn ->
                        insn.opcode == Opcode.INVOKE_VIRTUAL &&
                            (insn as? ReferenceInstruction)?.reference?.toString()
                                ?.contains(OBJECTLOGGER_SIG) == true
                    }
                    isAppkiller || hasLogger
                }
                if (relevantMethods.isEmpty()) return@classDefForEach

                relevantMethods.forEach { method ->
                    var pendingField: String? = null
                    method.instructions.forEach { insn ->
                        when (insn.opcode) {
                            Opcode.SGET_OBJECT -> {
                                val ref = (insn as ReferenceInstruction).reference
                                if (ref is FieldReference && ref.type == "Ljava/lang/String;") {
                                    pendingField = ref.toString()
                                }
                            }

                            Opcode.CONST_STRING -> pendingField?.let { field ->
                                val value =
                                    ((insn as ReferenceInstruction).reference as StringReference).string
                                stringMap[field] = value
                                placeholderClasses += field.substringBefore("->")
                                pendingField = null
                            }

                            else -> Unit // 其它指令不重置（宽松匹配，对应原正则的 .*?）
                        }
                    }
                }
                // 注入方法所在的类本身就是占位类
                placeholderClasses += classDef.type
            }
        }

        logger.info("pairip: collected ${stringMap.size} strings, ${placeholderClasses.size} placeholder classes")

        // ──────────────────────────────────────────────
        // Step 2：把使用方的 sget-object FIELD 还原成 const-string "VALUE"
        //         跳过 pairip 类和占位类自身（它们随后会被整类删除）
        // ──────────────────────────────────────────────
        if (stringMap.isNotEmpty()) {
            classDefForEach { classDef ->
                if (classDef.type.startsWith(PAIRIP_PREFIX)) return@classDefForEach
                if (classDef.type in placeholderClasses) return@classDefForEach

                classDef.methods.forEach methods@{ method ->
                    val insns = method.instructionsOrNull?.toList() ?: return@methods

                    // 先收集本方法内所有命中的 (index, 新指令)
                    val edits = ArrayList<Pair<Int, String>>()
                    insns.forEachIndexed { index, insn ->
                        if (insn.opcode != Opcode.SGET_OBJECT) return@forEachIndexed
                        val fieldRef = (insn as ReferenceInstruction).reference.toString()
                        val value = stringMap[fieldRef] ?: return@forEachIndexed
                        val reg = (insn as OneRegisterInstruction).registerA
                        edits += index to "const-string v$reg, \"${value.toSmaliLiteral()}\""
                    }
                    if (edits.isEmpty()) return@methods

                    // 命中了才取 mutable 方法，按相同签名定位
                    val mutableClass = mutableClassDefByOrNull(classDef.type) ?: return@methods
                    val mutableMethod = mutableClass.methods.firstOrNull { m ->
                        m.name == method.name &&
                            m.returnType == method.returnType &&
                            m.parameterTypes.map { it.toString() } ==
                            method.parameterTypes.map { it.toString() }
                    } ?: return@methods

                    // replaceInstruction 是 1:1 替换，不改变索引，正序即可
                    edits.forEach { (index, smali) ->
                        mutableMethod.replaceInstruction(index, smali)
                    }
                }
            }
        }

        // ──────────────────────────────────────────────
        // Step 3：把所有调用 VMRunner 的方法体清空成最小返回
        //         （等价于原 patcher.py 的 make_cleared_method）
        // ──────────────────────────────────────────────
        classDefForEach { classDef ->
            if (classDef.type.startsWith(PAIRIP_PREFIX)) return@classDefForEach

            // 收集本类内含 VMRunner 调用的方法签名
            val targets = classDef.methods.filter { method ->
                method.instructionsOrNull?.any { insn ->
                    insn.opcode == Opcode.INVOKE_STATIC &&
                        (insn as? ReferenceInstruction)?.reference?.toString()
                            ?.contains(VMRUNNER_CLASS) == true
                } == true
            }
            if (targets.isEmpty()) return@classDefForEach

            val mutableClass = mutableClassDefByOrNull(classDef.type) ?: return@classDefForEach
            targets.forEach { method ->
                val mutableMethod = mutableClass.methods.firstOrNull { m ->
                    m.name == method.name &&
                        m.returnType == method.returnType &&
                        m.parameterTypes.map { it.toString() } ==
                        method.parameterTypes.map { it.toString() }
                } ?: return@forEach

                // 清空所有指令（registerCount 保持不变，原方法 >= 1，用 v0 安全）
                val count = mutableMethod.instructions.size
                mutableMethod.removeInstructions(0, count)
                mutableMethod.addInstructions(0, minimalReturnFor(method.returnType))
            }
        }

        // ──────────────────────────────────────────────
        // Step 4：真正删除 com/pairip/ 类 + 字符串占位类
        //         先收集再统一删，避免 classDefForEach 遍历中并发修改
        // ──────────────────────────────────────────────
        val typesToRemove = HashSet<String>()
        classDefForEach { classDef ->
            if (classDef.type.startsWith(PAIRIP_PREFIX) || classDef.type in placeholderClasses) {
                typesToRemove += classDef.type
            }
        }

        val classMap = internalClassMap()
        var removed = 0
        typesToRemove.forEach { type ->
            if (classMap.remove(type) != null) removed++
        }
        logger.info("pairip: removed $removed classes (pairip + placeholders)")
    }
}
