include "wcel.mm"
include "wa.mm"
include "cnelbr.mm"
include "wbr.mm"
include "wn.mm"
include "wnel.mm"
include "nelbr.mm"
include "df-nel.mm"
include "syl6bbr.mm"

theorem nelbrnel
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. W ) -> ( A e// B <-> A e/ B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
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
    cV
    cW
    nelbr
    cA
    cB
    df-nel
    syl6bbr
end
