
axiom df-esum
  let cA: class A
  let cB: class B
  let vk: setvar k
  assert |- sum* k e. A B = U. ( ( RR*s |`s ( 0 [,] +oo ) ) tsums ( k e. A |-> B ) )
end
