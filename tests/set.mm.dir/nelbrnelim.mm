include "cnelbr.mm"
include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "nelbrim.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem nelbrnelim
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e// B -> A e/ B )

  proof
    cA
    cB
    cnelbr
    wbr
    cA
    cB
    wcel
    wn
    cA
    cB
    wnel
    cA
    cB
    nelbrim
    cA
    cB
    df-nel
    sylibr
end
