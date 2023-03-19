include "moddiffl.mm"

theorem rdr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A - ( A mod B ) ) / B ) = ( |_ ` ( A / B ) ) )

  proof
    cA
    cB
    moddiffl
end
