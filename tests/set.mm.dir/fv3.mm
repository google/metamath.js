include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "weu.mm"
include "cfv.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "elfv.mm"
include "wi.mm"
include "biimpr.mm"
include "alimi.mm"
include "vex.mm"
include "breq2.mm"
include "ceqsalv.mm"
include "sylib.mm"
include "anim2i.mm"
include "eximi.mm"
include "elequ2.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "exsimpr.mm"
include "df-eu.mm"
include "sylibr.mm"
include "jca.mm"
include "nfeu1.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfan.mm"
include "nfex.mm"
include "nfim.mm"
include "biimp.mm"
include "ax9.mm"
include "syl6.mm"
include "com23.mm"
include "impd.mm"
include "sps.mm"
include "anc2ri.mm"
include "com12.mm"
include "eximdv.mm"
include "syl5bi.mm"
include "exlimi.mm"
include "imp.mm"
include "impbii.mm"
include "bitri.mm"
include "abbi2i.mm"

theorem fv3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vz: setvar z

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint A z
  assert |- ( F ` A ) = { x | ( E. y ( x e. y /\ A F y ) /\ E! y A F y ) }

  proof
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    cA
    @1
    cF
    wbr
    #
    wa
    #
    vy
    wex
    #
    @3
    vy
    weu
    #
    wa
    #
    vx
    cA
    cF
    cfv
    #
    @0
    @8
    wcel
    @0
    vz
    cv
    #
    wcel
    #
    @3
    vy
    vz
    weq
    #
    wb
    #
    vy
    wal
    #
    wa
    #
    vz
    wex
    #
    @7
    vz
    vy
    @0
    cA
    cF
    elfv
    @15
    @7
    @15
    @5
    @6
    @15
    @10
    cA
    @9
    cF
    wbr
    #
    wa
    #
    vz
    wex
    @5
    @14
    @17
    vz
    @13
    @16
    @10
    @13
    @11
    @3
    wi
    #
    vy
    wal
    @16
    @12
    @18
    vy
    @3
    @11
    biimpr
    alimi
    @3
    @16
    vy
    @9
    vz
    vex
    @1
    @9
    cA
    cF
    breq2
    ceqsalv
    sylib
    anim2i
    eximi
    @17
    @4
    vz
    vy
    vz
    vy
    weq
    @10
    @2
    @16
    @3
    vz
    vy
    vx
    elequ2
    @9
    @1
    cA
    cF
    breq2
    anbi12d
    cbvexv
    sylib
    @15
    @13
    vz
    wex
    #
    @6
    @10
    @13
    vz
    exsimpr
    @3
    vy
    vz
    df-eu
    #
    sylibr
    jca
    @5
    @6
    @15
    @4
    @6
    @15
    wi
    vy
    @6
    @15
    vy
    @3
    vy
    nfeu1
    @14
    vy
    vz
    @10
    @13
    vy
    @10
    vy
    nfv
    @12
    vy
    nfa1
    nfan
    nfex
    nfim
    @6
    @19
    @4
    @15
    @20
    @4
    @13
    @14
    vz
    @13
    @4
    @14
    @13
    @4
    @10
    @12
    @4
    @10
    wi
    vy
    @12
    @2
    @3
    @10
    @12
    @3
    @2
    @10
    @12
    @3
    @11
    @2
    @10
    wi
    @3
    @11
    biimp
    vy
    vz
    vx
    ax9
    syl6
    com23
    impd
    sps
    anc2ri
    com12
    eximdv
    syl5bi
    exlimi
    imp
    impbii
    bitri
    abbi2i
end
