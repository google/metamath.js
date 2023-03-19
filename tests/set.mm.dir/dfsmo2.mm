include "wsmo.mm"
include "cdm.mm"
include "con0.mm"
include "wf.mm"
include "word.mm"
include "wel.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "df-smo.mm"
include "wa.mm"
include "ralcom.mm"
include "impexp.mm"
include "simpr.mm"
include "ordtr1.mm"
include "3impib.mm"
include "3com23.mm"
include "simp3.mm"
include "jca.mm"
include "3expia.mm"
include "impbid2.mm"
include "imbi1d.mm"
include "syl5bbr.mm"
include "ralbidv2.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "anbi2i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem dfsmo2
  let vx: setvar x
  let vy: setvar y
  let cF: class F

  disjoint F x
  disjoint F y
  disjoint x y
  assert |- ( Smo F <-> ( F : dom F --> On /\ Ord dom F /\ A. x e. dom F A. y e. x ( F ` y ) e. ( F ` x ) ) )

  proof
    cF
    wsmo
    cF
    cdm
    #
    con0
    cF
    wf
    #
    @0
    word
    #
    vy
    vx
    wel
    #
    vy
    cv
    #
    cF
    cfv
    vx
    cv
    #
    cF
    cfv
    wcel
    #
    wi
    #
    vx
    @0
    wral
    vy
    @0
    wral
    #
    w3a
    #
    @1
    @2
    @6
    vy
    @5
    wral
    #
    vx
    @0
    wral
    #
    w3a
    #
    vy
    vx
    cF
    df-smo
    @1
    @2
    @8
    wa
    #
    wa
    @1
    @2
    @11
    wa
    #
    wa
    @9
    @12
    @13
    @14
    @1
    @2
    @8
    @11
    @8
    @7
    vy
    @0
    wral
    #
    vx
    @0
    wral
    @2
    @11
    @7
    vy
    vx
    @0
    @0
    ralcom
    @2
    @15
    @10
    vx
    @0
    @2
    @5
    @0
    wcel
    #
    wa
    #
    @7
    @6
    vy
    @0
    @5
    @4
    @0
    wcel
    #
    @7
    wi
    @18
    @3
    wa
    #
    @6
    wi
    @17
    @7
    @18
    @3
    @6
    impexp
    @17
    @19
    @3
    @6
    @17
    @19
    @3
    @18
    @3
    simpr
    @2
    @16
    @3
    @19
    @2
    @16
    @3
    w3a
    @18
    @3
    @2
    @3
    @16
    @18
    @2
    @3
    @16
    @18
    @4
    @5
    @0
    ordtr1
    3impib
    3com23
    @2
    @16
    @3
    simp3
    jca
    3expia
    impbid2
    imbi1d
    syl5bbr
    ralbidv2
    ralbidva
    syl5bb
    pm5.32i
    anbi2i
    @1
    @2
    @8
    3anass
    @1
    @2
    @11
    3anass
    3bitr4i
    bitri
end
