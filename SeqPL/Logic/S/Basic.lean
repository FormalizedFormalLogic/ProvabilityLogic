module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.GL.Basic

@[expose]
public section

abbrev LogicS {α} : Logic α := (LogicGL) +ᴸ ({ □A 🡒 A | A })

end
