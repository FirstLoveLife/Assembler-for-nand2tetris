(*TODO: exception handle; space handle *)
(**)
CM.make "$/regexp-lib.cm";
structure RE = RegExpFn(
    structure P = AwkSyntax
    (* structure E = ThompsonEngine *)
    (* structure E = REGEXP_ENGINE *)
    structure E = BackTrackEngine (*Only this backend works fine for removeTailSpaces*)
)


fun allDigits s =
    let
        fun allInRange f (a,b) ans =
            if b <= a then
                ans
            else
                allInRange f (a+1,b) ((f a) andalso ans);

        fun checkDigit i = Char.isDigit (String.sub (s,i))
    in
        allInRange checkDigit (0, String.size s) true
    end

fun readLines filename =
    let
        fun removeCarriageReturn "" = ""
          | removeCarriageReturn line =
            let
                val length = String.size line
                val tail = String.substring (line, length-1, 1)
            in
                if tail <> "\r" andalso tail <> "\n"
                then line
                else String.substring (line, 0, length - 1)
            end

        fun removeHeadSpaces line =
            let
                val headSpace = "^ +"
                val compiledHeadSpace = RE.compileString headSpace
            in
                case StringCvt.scanString (RE.find compiledHeadSpace) line of
                    NONE => line
                 |  SOME match =>
                    let
                        val {pos, len} = MatchTree.root match
                        val length = String.size line - len
                    in
                        String.substring (line, len, length)
                    end
            end
        fun removeTailSpaces line =
            let
                val TailSpace = " +\r$"
                val compiledTailSpace = RE.compileString TailSpace
            in
                case StringCvt.scanString (RE.find compiledTailSpace) line of
                    NONE => line
                 |  SOME match =>
                    let
                        val {pos, len} = MatchTree.root match
                    in
                        String.substring (line, 0, pos)
                    end
            end
        fun removeComment line =
            let
                val comment = " *//.*"
                val compiledComment = RE.compileString comment
            in
                case StringCvt.scanString (RE.find compiledComment) line of
                    NONE => line
                  | SOME match =>
                    let
                        val {pos, len} = MatchTree.root match
                    in
                        String.substring (line, 0, pos)
                    end
            end
        fun readFile(filename) =
            let val file = TextIO.openIn filename
                val poem = TextIO.inputAll file
                val _ = TextIO.closeIn file
            in String.tokens (fn c => c = #"\n") poem
            end
    in
        List.filter
            (fn str => str <> "\r" andalso str <> "")
            (List.map (removeCarriageReturn
                       o removeHeadSpaces
                       o removeTailSpaces
                       o removeComment)
                      (readFile filename))
    end


fun replaceDigestLabelsAndVariables instructions =
    let
        fun replaceDigestLabels instructions =
            let
                fun replaceDigestLabelsHelper ([],
                                               newinstructions,
                                               index,
                                               newLabelPairs) =
                    (List.rev newinstructions, newLabelPairs)
                  | replaceDigestLabelsHelper (instructions,
                                               newinstructions,
                                               index,
                                               newLabelPairs) =
                    let
                        val firstInstruction = hd instructions
                        val length = String.size firstInstruction
                        val h = String.substring (firstInstruction, 0, 1)
                        val t = String.substring (firstInstruction, length-1, 1)
                        val nextIndex = index + 1
                    in
                        if h <> "(" orelse t <> ")"
                        then replaceDigestLabelsHelper (tl instructions,
                                                        firstInstruction::newinstructions,
                                                        nextIndex,
                                                        newLabelPairs)
                        else
                            let
                                val toReplcae = String.substring (firstInstruction, 1, (length - 2))
                                val label = (toReplcae, Int.toString index)
                            in
                                replaceDigestLabelsHelper (tl instructions,
                                                           newinstructions,
                                                           index,
                                                           label::newLabelPairs)
                            end
                    end
            in
                replaceDigestLabelsHelper (instructions, [], 0, [])
            end


        (*I don't replace in place, because sml's list is immutable and it may cost too much memory*)
        fun getLabelPairsVariables instructions =
            let

                val (instructions, newLabelPairs) = replaceDigestLabels instructions
                val defaultSymbolPairs =
                    [("SP", "0"), ("LCL", "1"), ("ARG", "2"), ("THIS", "3"),("THAT", "4"),
                     ("R0" , "0"), ("R1" , "1"), ("R2" , "2"), ("R3" , "3"), ("R4" , "4"),
                     ("R5" , "5"), ("R6" , "6"), ("R7" , "7"), ("R8" , "8"), ("R9" , "9"),
                     ("R10", "10"), ("R11", "11"), ("R12", "12"), ("R13", "13"), ("R14", "14"),
                     ("R15", "15"), ("SCREEN" , "16384"), ("KBD", "24576")]
                fun replaceVariablesHelper ([], index, allSymbolPairs) = allSymbolPairs
                  | replaceVariablesHelper (instructions, index, allSymbolPairs) =
                    let
                        val firstInstruction = hd instructions
                        val length = String.size firstInstruction
                        val h = String.substring (firstInstruction, 0, 1)
                        val nextIndex = index + 1
                        val symbol = String.substring (firstInstruction, 1, (length - 1))
                    in
                        if h <> "@"
                           orelse (allDigits symbol)
                           orelse (List.foldl (fn (a, b) => symbol = (#1 (a)) orelse b)
                                              false allSymbolPairs)
                        then replaceVariablesHelper (tl instructions,
                                                     index,
                                                     allSymbolPairs)
                        else
                            let
                                val symbolPair = (symbol, Int.toString index)
                            in
                                replaceVariablesHelper (tl instructions,
                                                        nextIndex,
                                                        symbolPair::allSymbolPairs)
                            end
                    end
            in
                (instructions, replaceVariablesHelper (instructions,
                                                       16,
                                                       newLabelPairs@defaultSymbolPairs))
            end

    in
        getLabelPairsVariables instructions
    end

fun process instructions allSymbolPairs =
    let
        fun  getBinary n =
             let
                 fun getBinaryHelper 0   acc = concat acc
                   | getBinaryHelper num acc = getBinaryHelper (num div 2)
                                                               (Int.toString (num mod 2) :: acc)
             in
                 getBinaryHelper n []
             end
        val compSymbolPairs =
            [("0", "0101010"),
             ("1", "0111111"),
             ("-1", "0111010"),
             ("D", "0001100"),
             ("A", "0110000"),
             ("M", "1110000"),
             ("!D", "0001101"),
             ("!A", "0110001"),
             ("!M", "1110001"),
             ("-D", "0001111"),
             ("-A", "0110011"),
             ("-M", "1110011"),
             ("D+1", "0011111"),
             ("A+1", "0110111"),
             ("M+1", "1110111"),
             ("D-1", "0001110"),
             ("A-1", "0110010"),
             ("M-1", "1110010"),
             ("D+A", "0000010"),
             ("D+M", "1000010"),
             ("D-A", "0010011"),
             ("D-M", "1010011"),
             ("A-D", "0000111"),
             ("M-D", "1000111"),
             ("D&A", "0000000"),
             ("D&M", "1000000"),
             ("D|A", "0010101"),
             ("D|M", "1010101")]
        val destSymbolPairs =
            [("", "000"),
             ("M", "001"),
             ("D", "010"),
             ("A", "100"),
             ("AD", "110"),
             ("MD", "011"),
             ("AM", "101"),
             ("AMD", "111")]
        val jumpSymbolPairs =
            [("", "000"),
             ("JGT", "001"),
             ("JEQ", "010"),
             ("JGE", "011"),
             ("JLT", "100"),
             ("JNE", "101"),
             ("JLE", "110"),
             ("JMP", "111")]

        fun appendZero 0 ans = ans
          | appendZero n ans = appendZero (n-1) ("0" ^ ans)

        fun getBinaryInstruction (token : string, symbolPairs : (string *string) list) =
            let
                val ans = List.filter (fn elem => (#1 elem) = token) symbolPairs
            in
                (#2 (hd ans))
            end

        fun parseInstruction instruction =
            if String.substring (instruction, 0, 1) = "@"
            then
                let
                    val symbol = String.substring (instruction, 1, String.size instruction - 1)
                in
                    if allDigits symbol
                    then
                        let
                            val address = symbol
                            val binary = getBinary (Option.valOf (Int.fromString address))
                            val len = size binary
                            val ans = appendZero (16-len) "" ^ binary ^ "\r"
                        in
                            ans
                        end
                    else
                        let
                            val address = getBinaryInstruction (symbol, allSymbolPairs)
                            val binary = getBinary (Option.valOf (Int.fromString address))
                            val len = size binary
                            val ans = appendZero (16-len) "" ^ binary ^ "\r"
                        in
                            ans
                        end
                end
            else
                case String.tokens (fn c => c = #"=") instruction of
                    jump::[] =>
                    (case String.tokens (fn c => c = #";")  jump of
                         comp::jmp => "111"
                                      ^ (getBinaryInstruction (comp, compSymbolPairs))
                                      ^ "000"
                                      ^ (getBinaryInstruction (hd jmp, jumpSymbolPairs))
                                      ^ "\r")
                  | dest::comp => "111"
                                  ^ (getBinaryInstruction (hd comp, compSymbolPairs))
                                  ^ (getBinaryInstruction (dest, destSymbolPairs))
                                  ^ "000"
                                  ^ "\r"
    in
        List.map (fn instruction => parseInstruction instruction) instructions
    end

fun init filename =
    let
        val (instructions, allSymbolPairs) = replaceDigestLabelsAndVariables  (readLines filename)
        val instructions =  process instructions allSymbolPairs
    in
        case String.tokens (fn c => c = #".") filename of
            pre::pos =>
            let
                val file = TextIO.openOut(pre ^ ".hack")
            in
                let
                    fun write [] = ()
                      | write instructions =
                        let
                            val _ = TextIO.output (file, hd instructions)
                        in
                            write (tl instructions)
                        end
                in
                    write instructions;
                    TextIO.closeOut(file)
                end
            end
    end
