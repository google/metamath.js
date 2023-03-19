include "cgt.mm"
include "wbr.mm"
include "clt.mm"
include "ccnv.mm"
include "df-gt.mm"
include "breqi.mm"
include "brcnv.mm"
include "bitri.mm"

theorem gt-lth
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume gt-lth.1: |- A e. _V
  assume gt-lth.2: |- B e. _V


  assert |- ( A > B <-> B < A )

  proof
    cA
    cB
    cgt
    wbr
    cA
    cB
    clt
    ccnv
    #
    wbr
    cB
    cA
    clt
    wbr
    cA
    cB
    cgt
    @0
    df-gt
    breqi
    cA
    cB
    clt
    gt-lth.1
    gt-lth.2
    brcnv
    bitri
end
