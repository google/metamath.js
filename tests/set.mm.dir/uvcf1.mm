include "cnzr.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "crg.mm"
include "nzrring.mm"
include "uvcff.mm"
include "sylan.mm"
include "wne.mm"
include "cur.mm"
include "c0g.mm"
include "eqid.mm"
include "nzrnz.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplrl.mm"
include "uvcvv1.mm"
include "simplrr.mm"
include "simpr.mm"
include "necomd.mm"
include "uvcvv0.mm"
include "3netr4d.mm"
include "fveq1.mm"
include "necon3i.mm"
include "syl.mm"
include "ex.mm"
include "necon4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem uvcf1
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cW: class W
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  assume uvcff.u: |- U = ( R unitVec I )
  assume uvcff.y: |- Y = ( R freeLMod I )
  assume uvcff.b: |- B = ( Base ` Y )


  assert |- ( ( R e. NzRing /\ I e. W ) -> U : I -1-1-> B )

  proof
    cR
    cnzr
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cI
    cB
    cU
    wf
    #
    vi
    cv
    #
    cU
    cfv
    #
    vj
    cv
    #
    cU
    cfv
    #
    wceq
    @4
    @6
    wceq
    wi
    #
    vj
    cI
    wral
    vi
    cI
    wral
    cI
    cB
    cU
    wf1
    @0
    cR
    crg
    wcel
    #
    @1
    @3
    cR
    nzrring
    #
    cB
    cR
    cU
    cI
    cW
    cY
    uvcff.u
    uvcff.y
    uvcff.b
    uvcff
    sylan
    @2
    @8
    vi
    vj
    cI
    cI
    @2
    @4
    cI
    wcel
    #
    @6
    cI
    wcel
    #
    wa
    #
    wa
    #
    @4
    @6
    @5
    @7
    @14
    @4
    @6
    wne
    #
    @5
    @7
    wne
    #
    @14
    @15
    wa
    #
    @4
    @5
    cfv
    #
    @4
    @7
    cfv
    #
    wne
    @16
    @17
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    @18
    @19
    @0
    @20
    @21
    wne
    @1
    @13
    @15
    cR
    @20
    @21
    @20
    eqid
    #
    @21
    eqid
    #
    nzrnz
    ad3antrrr
    @17
    cR
    cU
    @20
    cI
    @4
    crg
    cW
    uvcff.u
    @0
    @9
    @1
    @13
    @15
    @10
    ad3antrrr
    #
    @0
    @1
    @13
    @15
    simpllr
    #
    @2
    @11
    @12
    @15
    simplrl
    #
    @22
    uvcvv1
    @17
    cR
    cU
    cI
    @6
    @4
    crg
    cW
    @21
    uvcff.u
    @24
    @25
    @2
    @11
    @12
    @15
    simplrr
    @26
    @17
    @4
    @6
    @14
    @15
    simpr
    necomd
    @23
    uvcvv0
    3netr4d
    @5
    @7
    @18
    @19
    @4
    @5
    @7
    fveq1
    necon3i
    syl
    ex
    necon4d
    ralrimivva
    vi
    vj
    cI
    cB
    cU
    dff13
    sylanbrc
end
