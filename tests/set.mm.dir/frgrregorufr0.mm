include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "chash.mm"
include "c1.mm"
include "c0.mm"
include "wo.mm"
include "cdif.mm"
include "cfrgr.mm"
include "wcel.mm"
include "wral.mm"
include "wne.mm"
include "cpr.mm"
include "csn.mm"
include "wrex.mm"
include "w3o.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "frgrwopreg.mm"
include "wi.mm"
include "wa.mm"
include "frgrwopreg1.mm"
include "3mix3d.mm"
include "expcom.mm"
include "wn.mm"
include "eqeq1i.mm"
include "rabeq0.mm"
include "bitri.mm"
include "neqne.mm"
include "ralimi.mm"
include "3mix2d.mm"
include "a1d.mm"
include "sylbi.mm"
include "jaoi.mm"
include "frgrwopreg2.mm"
include "difrab0eq.mm"
include "eqeq2i.mm"
include "rabid2.mm"
include "3mix1.mm"
include "mpcom.mm"

theorem frgrregorufr0
  let vw: setvar w
  let vv: setvar v
  let cD: class D
  let cE: class E
  let cG: class G
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume frgrregorufr0.v: |- V = ( Vtx ` G )
  assume frgrregorufr0.e: |- E = ( Edg ` G )
  assume frgrregorufr0.d: |- D = ( VtxDeg ` G )

  disjoint D v
  disjoint D w
  disjoint v w
  disjoint E v
  disjoint G v
  disjoint G w
  disjoint K v
  disjoint K w
  disjoint V v
  disjoint V w
  disjoint D x
  disjoint D y
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint E y
  disjoint G y
  disjoint K x
  disjoint K y
  disjoint V x
  disjoint V y
  assert |- ( G e. FriendGraph -> ( A. v e. V ( D ` v ) = K \/ A. v e. V ( D ` v ) =/= K \/ E. v e. V A. w e. ( V \ { v } ) { v , w } e. E ) )

  proof
    vx
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    #
    vx
    cV
    crab
    #
    chash
    cfv
    c1
    wceq
    #
    @3
    c0
    wceq
    #
    wo
    #
    cV
    @3
    cdif
    #
    chash
    cfv
    c1
    wceq
    #
    @7
    c0
    wceq
    #
    wo
    #
    wo
    cG
    cfrgr
    wcel
    #
    vv
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    @13
    cK
    wne
    #
    vv
    cV
    wral
    #
    @12
    vw
    cv
    cpr
    cE
    wcel
    vw
    cV
    @12
    csn
    cdif
    wral
    vv
    cV
    wrex
    #
    w3o
    #
    vy
    @3
    @7
    cD
    cG
    cK
    cV
    frgrregorufr0.v
    frgrregorufr0.d
    @2
    vy
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    vx
    vy
    cV
    vx
    vy
    weq
    @1
    @21
    cK
    @0
    @20
    cD
    fveq2
    eqeq1d
    cbvrabv
    #
    @7
    eqid
    #
    frgrwopreg
    @6
    @11
    @19
    wi
    #
    @10
    @4
    @24
    @5
    @11
    @4
    @19
    @11
    @4
    wa
    @18
    @15
    @17
    vy
    vw
    vv
    @3
    @7
    cD
    cE
    cG
    cK
    cV
    frgrregorufr0.v
    frgrregorufr0.d
    @22
    @23
    frgrregorufr0.e
    frgrwopreg1
    3mix3d
    expcom
    @5
    @14
    wn
    #
    vv
    cV
    wral
    #
    @24
    @5
    @14
    vv
    cV
    crab
    #
    c0
    wceq
    @26
    @3
    @27
    c0
    @2
    @14
    vx
    vv
    cV
    vx
    vv
    weq
    @1
    @13
    cK
    @0
    @12
    cD
    fveq2
    eqeq1d
    cbvrabv
    #
    eqeq1i
    @14
    vv
    cV
    rabeq0
    bitri
    @26
    @19
    @11
    @26
    @17
    @15
    @18
    @25
    @16
    vv
    cV
    @13
    cK
    neqne
    ralimi
    3mix2d
    a1d
    sylbi
    jaoi
    @8
    @24
    @9
    @11
    @8
    @19
    @11
    @8
    wa
    @18
    @15
    @17
    vy
    vw
    vv
    @3
    @7
    cD
    cE
    cG
    cK
    cV
    frgrregorufr0.v
    frgrregorufr0.d
    @22
    @23
    frgrregorufr0.e
    frgrwopreg2
    3mix3d
    expcom
    @9
    cV
    @3
    wceq
    #
    @24
    @2
    vx
    cV
    difrab0eq
    @29
    @15
    @24
    @29
    cV
    @27
    wceq
    @15
    @3
    @27
    cV
    @28
    eqeq2i
    @14
    vv
    cV
    rabid2
    bitri
    @15
    @19
    @11
    @15
    @17
    @18
    3mix1
    a1d
    sylbi
    sylbi
    jaoi
    jaoi
    mpcom
end
