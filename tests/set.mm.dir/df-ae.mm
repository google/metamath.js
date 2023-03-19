
axiom df-ae
  let vm: setvar m
  let va: setvar a
  assert |- ae = { <. a , m >. | ( m ` ( U. dom m \ a ) ) = 0 }
end
