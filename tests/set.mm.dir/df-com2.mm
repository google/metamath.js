
axiom df-com2
  let vg: setvar g
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  assert |- Com2 = { <. g , h >. | A. a e. ran g A. b e. ran g ( a h b ) = ( b h a ) }
end
