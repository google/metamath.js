include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "csdm.mm"
include "wn.mm"
include "wa.mm"
include "endom.mm"
include "sdomnen.mm"
include "con2i.mm"
include "jca.mm"
include "wo.mm"
include "brdom2.mm"
include "biimpi.mm"
include "orcanai.mm"
include "impbii.mm"

theorem bren2
  let cA: class A
  let cB: class B


  assert |- ( A ~~ B <-> ( A ~<_ B /\ -. A ~< B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    csdm
    wbr
    #
    wn
    #
    wa
    @0
    @1
    @3
    cA
    cB
    endom
    @2
    @0
    cA
    cB
    sdomnen
    con2i
    jca
    @1
    @2
    @0
    @1
    @2
    @0
    wo
    cA
    cB
    brdom2
    biimpi
    orcanai
    impbii
end
