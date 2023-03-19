include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cfv.mm"
include "wceq.mm"
include "wex.mm"
include "wrex.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wss.mm"
include "w3a.mm"
include "eqid.mm"
include "pmtrfrn.mm"
include "simpld.mm"
include "simp3d.mm"
include "en2.mm"
include "syl.mm"
include "simp2d.mm"
include "simprd.mm"
include "jca32.mm"
include "sseq1.mm"
include "breq1.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "vex.mm"
include "prss.mm"
include "bicomi.mm"
include "wb.mm"
include "pr2ne.mm"
include "mp2an.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "syl6ib.mm"
include "2eximdv.mm"
include "mpd.mm"
include "r2ex.mm"
include "sylibr.mm"

theorem pmtrrn2
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cR: class R
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let cP: class P
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint T x
  disjoint T y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x z
  disjoint y z
  disjoint D z
  disjoint P x
  disjoint P y
  disjoint T w
  disjoint T z
  disjoint V y
  disjoint V z
  assert |- ( F e. R -> E. x e. D E. y e. D ( x =/= y /\ F = ( T ` { x , y } ) ) )

  proof
    cF
    cR
    wcel
    #
    vx
    cv
    #
    cD
    wcel
    vy
    cv
    #
    cD
    wcel
    wa
    #
    @1
    @2
    wne
    #
    cF
    @1
    @2
    cpr
    #
    cT
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @8
    vy
    cD
    wrex
    vx
    cD
    wrex
    @0
    cF
    cid
    cdif
    cdm
    #
    @5
    wceq
    #
    vy
    wex
    vx
    wex
    #
    @10
    @0
    @11
    c2o
    cen
    wbr
    #
    @13
    @0
    cD
    cvv
    wcel
    #
    @11
    cD
    wss
    #
    @14
    @0
    @15
    @16
    @14
    w3a
    #
    cF
    @11
    cT
    cfv
    #
    wceq
    #
    cD
    @11
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    @11
    eqid
    pmtrfrn
    #
    simpld
    #
    simp3d
    #
    vx
    vy
    @11
    en2
    syl
    @0
    @12
    @9
    vx
    vy
    @0
    @12
    @5
    cD
    wss
    #
    @5
    c2o
    cen
    wbr
    #
    @7
    wa
    #
    wa
    #
    @9
    @0
    @16
    @14
    @19
    wa
    #
    wa
    @12
    @26
    @0
    @16
    @14
    @19
    @0
    @15
    @16
    @14
    @21
    simp2d
    @22
    @0
    @17
    @19
    @20
    simprd
    jca32
    @12
    @16
    @23
    @27
    @25
    @11
    @5
    cD
    sseq1
    @12
    @14
    @24
    @19
    @7
    @11
    @5
    c2o
    cen
    breq1
    @12
    @18
    @6
    cF
    @11
    @5
    cT
    fveq2
    eqeq2d
    anbi12d
    anbi12d
    syl5ibcom
    @23
    @3
    @25
    @8
    @3
    @23
    @1
    @2
    cD
    vx
    vex
    #
    vy
    vex
    #
    prss
    bicomi
    @24
    @4
    @7
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @24
    @4
    wb
    @28
    @29
    @1
    @2
    cvv
    cvv
    pr2ne
    mp2an
    anbi1i
    anbi12i
    syl6ib
    2eximdv
    mpd
    @8
    vx
    vy
    cD
    cD
    r2ex
    sylibr
end
