
structure NJ_Util = struct
  fun parseFile filename =
    let
      val stream = TextIO.openIn filename
      val interactive = false
      val consumer = ErrorMsg.defaultConsumer ()
      val source = Source.newSource (filename, stream, interactive, consumer)
    in
      SmlFile.parse source
    end
end

