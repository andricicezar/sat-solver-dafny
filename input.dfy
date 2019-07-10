include "parser.dfy"
include "file_input.dfy"
include "my_datatypes.dfy"

module Input {
    import Parser
    import FileInput
    import opened MyDatatypes

    function method getInput() : Maybe<(int, seq<seq<int>>)> 
        reads *;
    {
        Parser.parseContent(
            FileInput.Reader.getContent()[0..])
    }

    function method getTimestamp() : int
    {
      FileInput.Reader.getTimestamp()
    }
}
