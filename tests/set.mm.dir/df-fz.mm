
axiom df-fz
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  assert |- ... = ( m e. ZZ , n e. ZZ |-> { k e. ZZ | ( m <_ k /\ k <_ n ) } )
end
