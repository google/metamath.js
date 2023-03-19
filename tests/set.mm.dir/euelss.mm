include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "weu.mm"
include "w3a.mm"
include "wtru.mm"
include "wa.mm"
include "wreu.mm"
include "wrex.mm"
include "id.mm"
include "df-rex.mm"
include "ancom.mm"
include "truan.mm"
include "bitri.mm"
include "exbii.mm"
include "sylbbr.mm"
include "df-reu.mm"
include "eubii.mm"
include "reuss.mm"
include "syl3an.mm"
include "sylib.mm"
include "bitr3i.mm"
include "sylibr.mm"

theorem euelss
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ B /\ E. x x e. A /\ E! x x e. B ) -> E! x x e. A )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    #
    @1
    cB
    wcel
    #
    vx
    weu
    #
    w3a
    #
    @2
    wtru
    wa
    #
    vx
    weu
    #
    @2
    vx
    weu
    @6
    wtru
    vx
    cA
    wreu
    #
    @8
    @0
    @0
    @3
    wtru
    vx
    cA
    wrex
    #
    @5
    wtru
    vx
    cB
    wreu
    #
    @9
    @0
    id
    @10
    @7
    vx
    wex
    @3
    wtru
    vx
    cA
    df-rex
    @7
    @2
    vx
    @7
    wtru
    @2
    wa
    #
    @2
    @2
    wtru
    ancom
    @2
    truan
    #
    bitri
    exbii
    sylbbr
    @11
    @4
    wtru
    wa
    #
    vx
    weu
    @5
    wtru
    vx
    cB
    df-reu
    @14
    @4
    vx
    @14
    wtru
    @4
    wa
    @4
    @4
    wtru
    ancom
    @4
    truan
    bitri
    eubii
    sylbbr
    wtru
    vx
    cA
    cB
    reuss
    syl3an
    wtru
    vx
    cA
    df-reu
    sylib
    @2
    @7
    vx
    @2
    @12
    @7
    @13
    wtru
    @2
    ancom
    bitr3i
    eubii
    sylibr
end
