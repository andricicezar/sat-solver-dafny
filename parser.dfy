include "my_datatypes.dfy"

module Parser {
    import opened MyDatatypes

    function method skipLine(content : string) : string 
        decreases |content|;
        ensures |content| > 0 ==> |skipLine(content)| < |content|;
    {
        if |content| == 0 then content
        else
            if content[0] == '\n' then content[1..] 
            else skipLine(content[1..])
    }

    lemma prop_skipWhiteSpaces(content : string)
        ensures |skipWhiteSpaces(content)| <= |content|;
    {}

    function method skipWhiteSpaces(content : string) : string 
        decreases |content|;
    {
        if |content| == 0 then content
        else
            if content[0] == ' ' then skipWhiteSpaces(content[1..])
            else if content[0] == '\n' then skipWhiteSpaces(content[1..])
            else content
    }

    function method isDigit(chr : char) : bool
    {
        '0' <= chr <= '9'
    }
        

    function method toInt(chr: char) : int
        requires isDigit(chr)
    {
        (chr as int) - ('0' as int)
    }

    lemma prop_extractDigits(content : string) 
        ensures |content| == |extractDigits(content).0| + |extractDigits(content).1|;
    {}

    function method extractDigits(content : string) : (seq<int>, string)
        decreases |content|;
    {
        if (|content| == 0) then ([], content)
        else if (isDigit(content[0])) then
            var (h, tail) := extractDigits(content[1..]);
            ([toInt(content[0])] + h, tail)
        else ([], content)
    }

    function method joinInts(number : int, ints : seq<int>) : int 
        decreases |ints|;
    {
        if |ints| == 0 then number
        else joinInts(number * 10 + ints[0], ints[1..])
    }

    lemma prop_getNextNumber(content : string)
        requires getNextNumber(content).Just?;
        ensures |getNextNumber(content).value.1| < |content|;
    {
        prop_extractDigits(content[1..]);
        assert content[0] == '-' ==> 
            |getNextNumber(content[1..]).value.1| == |extractDigits(content[1..]).1| < |content[1..]| < |content|;

        prop_extractDigits(content);
        assert content[0] != '-' ==> 
            |getNextNumber(content).value.1| == |extractDigits(content).1| < |content|;
    }

    function method getNextNumber(content : string) : Maybe<(int, string)>
        decreases |content|;
    {
        if (|content| == 0) then Error("content finished unexpectatly")
        else if (content[0] == '-') then
            var (digits, newContent) := extractDigits(content[1..]);
            prop_extractDigits(content[1..]);

            if |digits| == 0 then Error("only alpha characters ahead, no numbers after -")
            else
                var number := joinInts(0, digits);

                assert |newContent| < |content|;
                Just((-number, newContent))
        else
            var (digits, newContent) := extractDigits(content);
            prop_extractDigits(content);

            if |digits| == 0 then Error("only alpha characters ahead, no numbers")
            else 
                var number := joinInts(0, digits);

                assert |newContent| < |content|;
                Just((number, newContent))
    }

    function method extractNumbers(content : string) : (seq<int>, string)
        decreases |content|;
    {
        prop_skipWhiteSpaces(content);
        var content' := skipWhiteSpaces(content);

        match getNextNumber(content')
            case Error(_) => ([], content')
            case Just((number, content'')) =>
                prop_getNextNumber(content');
                prop_skipWhiteSpaces(content'');
                var content''' := skipWhiteSpaces(content'');

                assert |content'''| < |content'| <= |content|;
                var (fst, snd) := extractNumbers(content''');
                ([number] + fst, snd)
    }

    function method getNextClause(numbers : seq<int>) : Maybe<(seq<int>, seq<int>)>
        decreases |numbers|;
    {
        if (|numbers| == 0) then Error("no 0 there")
        else 
            if (numbers[0] == 0) then Just(([], numbers[1..]))
            else
                var head := [numbers[0]];
                match getNextClause(numbers[1..])
                    case Error(m) => Error(m)
                    case Just((tail, numbers)) => 
                        Just((head + tail, numbers))
    }

    function method getClauses(clausesCount : int, numbers : seq<int>) :
        Maybe<(seq<seq<int>>, seq<int>)>

        decreases clausesCount, |numbers|;
    {
        if (clausesCount <= 0 || |numbers| == 0) then Just(([], numbers))
        else 
            match getNextClause(numbers)
                case Error(m) => Error(m)
                case Just((clause, numbers)) =>
                    match getClauses(clausesCount - 1, numbers)
                        case Error(m) => Error(m)
                        case Just((clauses, numbers)) =>
                            Just(([clause] + clauses, numbers))
    }

    function method getToInput(content : string) : Maybe<string>
        decreases |content|;
    {
        prop_skipWhiteSpaces(content);
        var content := skipWhiteSpaces(content);

        if |content| == 0 then Error("nothing found")
        else if content[0] == 'c' then
            getToInput(skipLine(content))
        else if content[0] == 'p' then (
            var content := skipWhiteSpaces(content[1..]);

            if |content| < 3 then Error("input not correctly formated")
            else Just(skipWhiteSpaces(content[3..])))
        else Error("invalid symbol")
    }

    function method parseContent(content : string) :
        Maybe<(int, seq<seq<int>>)>
    {
        match getToInput(content)
            case Error(m) => Error(m)
            case Just(content) =>
                match getNextNumber(content)
                    case Error(m) => Error(m)
                    case Just((variablesCount, content)) =>
                        match getNextNumber(skipWhiteSpaces(content))
                            case Error(m) => Error(m)
                            case Just((clausesCount, content)) =>
                                var (numbers, _) := extractNumbers(content);
                                match getClauses(clausesCount, numbers)
                                    case Error(m) => Error(m)
                                    case Just((clauses, content)) =>
                                        Just((variablesCount, clauses))
    }
}