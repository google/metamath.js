include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "cab.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "enref.mm"
include "breq1.mm"
include "spcev.mm"
include "ax-mp.mm"
include "abn0.mm"
include "mpbir.mm"
include "scott0.mm"
include "necon3bii.mm"
include "mpbi.mm"
include "rabn0.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "vex.mm"
include "elab.mm"
include "ralab.mm"
include "anbi12i.mm"
include "simpl.mm"
include "a1i.mm"
include "wb.mm"
include "eqeq12i.mm"
include "abbi.mm"
include "bitr4i.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "albidv.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "spv.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "jcad.mm"
include "ensym.mm"
include "entr.mm"
include "sylan.mm"
include "syl6.mm"
include "syl5bi.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpi.mm"
include "enen2.mm"
include "imbi1d.mm"
include "abbidv.mm"
include "3eqtr4g.mm"
include "impbii.mm"

theorem karden
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z
  let vw: setvar w
  assume karden.1: |- A e. _V
  assume karden.2: |- B e. _V
  assume karden.3: |- C = { x | ( x ~~ A /\ A. y ( y ~~ A -> ( rank ` x ) C_ ( rank ` y ) ) ) }
  assume karden.4: |- D = { x | ( x ~~ B /\ A. y ( y ~~ B -> ( rank ` x ) C_ ( rank ` y ) ) ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint C z
  disjoint D z
  assert |- ( C = D <-> A ~~ B )

  proof
    cC
    cD
    wceq
    #
    cA
    cB
    cen
    wbr
    #
    @0
    vz
    cv
    #
    crnk
    cfv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    wss
    #
    vy
    vw
    cv
    #
    cA
    cen
    wbr
    #
    vw
    cab
    #
    wral
    #
    vz
    @9
    wrex
    #
    @1
    @10
    vz
    @9
    crab
    #
    c0
    wne
    #
    @11
    @9
    c0
    wne
    #
    @13
    @14
    @8
    vw
    wex
    #
    cA
    cA
    cen
    wbr
    #
    @15
    cA
    karden.1
    enref
    @8
    @16
    vw
    cA
    karden.1
    @7
    cA
    cA
    cen
    breq1
    spcev
    ax-mp
    @8
    vw
    abn0
    mpbir
    @9
    c0
    @12
    c0
    vz
    vy
    @9
    scott0
    necon3bii
    mpbi
    @10
    vz
    @9
    rabn0
    mpbi
    @0
    @10
    @1
    vz
    @9
    @0
    @2
    @9
    wcel
    #
    @10
    @1
    @17
    @10
    wa
    @2
    cA
    cen
    wbr
    #
    @4
    cA
    cen
    wbr
    #
    @6
    wi
    #
    vy
    wal
    #
    wa
    #
    @0
    @1
    @17
    @18
    @10
    @21
    @8
    @18
    vw
    @2
    vz
    vex
    @7
    @2
    cA
    cen
    breq1
    elab
    @8
    @19
    @6
    vy
    vw
    @7
    @4
    cA
    cen
    breq1
    ralab
    anbi12i
    @0
    @22
    @18
    @2
    cB
    cen
    wbr
    #
    wa
    @1
    @0
    @22
    @18
    @23
    @22
    @18
    wi
    @0
    @18
    @21
    simpl
    a1i
    @0
    @22
    @23
    @4
    cB
    cen
    wbr
    #
    @6
    wi
    #
    vy
    wal
    #
    wa
    #
    @23
    @0
    vx
    cv
    #
    cA
    cen
    wbr
    #
    @19
    @28
    crnk
    cfv
    #
    @5
    wss
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    @28
    cB
    cen
    wbr
    #
    @24
    @31
    wi
    #
    vy
    wal
    #
    wa
    #
    wb
    #
    vx
    wal
    #
    @22
    @27
    wb
    #
    @0
    @34
    vx
    cab
    #
    @38
    vx
    cab
    #
    wceq
    @40
    cC
    @42
    cD
    @43
    karden.3
    karden.4
    eqeq12i
    @34
    @38
    vx
    abbi
    bitr4i
    @39
    @41
    vx
    vz
    @28
    @2
    wceq
    #
    @34
    @22
    @38
    @27
    @44
    @29
    @18
    @33
    @21
    @28
    @2
    cA
    cen
    breq1
    @44
    @32
    @20
    vy
    @44
    @31
    @6
    @19
    @44
    @30
    @3
    @5
    @28
    @2
    crnk
    fveq2
    sseq1d
    #
    imbi2d
    albidv
    anbi12d
    @44
    @35
    @23
    @37
    @26
    @28
    @2
    cB
    cen
    breq1
    @44
    @36
    @25
    vy
    @44
    @31
    @6
    @24
    @45
    imbi2d
    albidv
    anbi12d
    bibi12d
    spv
    sylbi
    @23
    @26
    simpl
    syl6bi
    jcad
    @18
    cA
    @2
    cen
    wbr
    @23
    @1
    @2
    cA
    ensym
    cA
    @2
    cB
    entr
    sylan
    syl6
    syl5bi
    expd
    rexlimdv
    mpi
    @1
    @42
    @43
    cC
    cD
    @1
    @34
    @38
    vx
    @1
    @29
    @35
    @33
    @37
    cA
    cB
    @28
    enen2
    @1
    @32
    @36
    vy
    @1
    @19
    @24
    @31
    cA
    cB
    @4
    enen2
    imbi1d
    albidv
    anbi12d
    abbidv
    karden.3
    karden.4
    3eqtr4g
    impbii
end
