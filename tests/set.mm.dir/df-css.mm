
axiom df-css
  let vh: setvar h
  let vs: setvar s
  assert |- CSubSp = ( h e. _V |-> { s | s = ( ( ocv ` h ) ` ( ( ocv ` h ) ` s ) ) } )
end
