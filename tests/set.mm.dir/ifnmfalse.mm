include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "cif.mm"
include "wceq.mm"
include "df-nel.mm"
include "iffalse.mm"
include "sylbi.mm"

theorem ifnmfalse
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e/ B -> if ( A e. B , C , D ) = D )

  proof
    cA
    cB
    wnel
    cA
    cB
    wcel
    #
    wn
    @0
    cC
    cD
    cif
    cD
    wceq
    cA
    cB
    df-nel
    @0
    cC
    cD
    iffalse
    sylbi
end
