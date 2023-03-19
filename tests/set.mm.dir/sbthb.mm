include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cen.mm"
include "sbth.mm"
include "endom.mm"
include "ensym.mm"
include "syl.mm"
include "jca.mm"
include "impbii.mm"

theorem sbthb
  let cA: class A
  let cB: class B


  assert |- ( ( A ~<_ B /\ B ~<_ A ) <-> A ~~ B )

  proof
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    sbth
    @2
    @0
    @1
    cA
    cB
    endom
    @2
    cB
    cA
    cen
    wbr
    @1
    cA
    cB
    ensym
    cB
    cA
    endom
    syl
    jca
    impbii
end
