include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wel.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "wral.mm"
include "ctb.mm"
include "co.mm"
include "crp.mm"
include "blin2.mm"
include "wb.mm"
include "simpll.mm"
include "cuni.mm"
include "inss1.mm"
include "sseli.mm"
include "elunii.mm"
include "sylan.mm"
include "ad2ant2lr.mm"
include "wceq.mm"
include "unirnbl.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "blssex.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimdva.mm"
include "ralrimivv.mm"
include "cvv.mm"
include "fvex.mm"
include "rnex.mm"
include "isbasis2g.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem blbas
  let cD: class D
  let cX: class X
  let cC: class C
  let vx: setvar x
  let vb: setvar b
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cR: class R
  let cY: class Y


  assert |- ( D e. ( *Met ` X ) -> ran ( ball ` D ) e. TopBases )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    vz
    vb
    wel
    vb
    cv
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    wa
    vb
    cD
    cbl
    cfv
    #
    crn
    #
    wrex
    #
    vz
    @3
    wral
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    @5
    ctb
    wcel
    #
    @0
    @7
    vx
    vy
    @5
    @5
    @0
    @1
    @5
    wcel
    #
    @2
    @5
    wcel
    #
    wa
    #
    @6
    vz
    @3
    @0
    vz
    cv
    #
    @3
    wcel
    #
    wa
    #
    @12
    @6
    @15
    @12
    wa
    #
    @6
    @13
    vr
    cv
    @4
    co
    @3
    wss
    vr
    crp
    wrex
    #
    vr
    @1
    @2
    cD
    @13
    cX
    blin2
    @16
    @0
    @13
    cX
    wcel
    @6
    @17
    wb
    @0
    @14
    @12
    simpll
    @16
    @13
    @5
    cuni
    #
    cX
    @14
    @10
    @13
    @18
    wcel
    #
    @0
    @11
    @14
    vz
    vx
    wel
    @10
    @19
    @3
    @1
    @13
    @1
    @2
    inss1
    sseli
    @13
    @1
    @5
    elunii
    sylan
    ad2ant2lr
    @0
    @18
    cX
    wceq
    @14
    @12
    cD
    cX
    unirnbl
    ad2antrr
    eleqtrd
    vb
    @3
    cD
    @13
    cX
    vr
    blssex
    syl2anc
    mpbird
    ex
    ralrimdva
    ralrimivv
    @5
    cvv
    wcel
    @9
    @8
    wb
    @4
    cD
    cbl
    fvex
    rnex
    vx
    vy
    vz
    vb
    @5
    cvv
    isbasis2g
    ax-mp
    sylibr
end
