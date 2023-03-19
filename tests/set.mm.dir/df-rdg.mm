
axiom df-rdg
  let vg: setvar g
  let cF: class F
  let cI: class I
  assert |- rec ( F , I ) = recs ( ( g e. _V |-> if ( g = (/) , I , if ( Lim dom g , U. ran g , ( F ` ( g ` U. dom g ) ) ) ) ) )
end
