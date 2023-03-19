include "cmzpcl.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cmul.mm"
include "wa.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "cz.mm"
include "cmap.mm"
include "wss.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "simp1.mm"
include "cvv.mm"
include "wb.mm"
include "elfvexd.mm"
include "elmzpcl.mm"
include "syl.mm"
include "mpbid.mm"
include "simprrd.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem mzpcl34
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a
  let vb: setvar b


  assert |- ( ( P e. ( mzPolyCld ` V ) /\ F e. P /\ G e. P ) -> ( ( F oF + G ) e. P /\ ( F oF x. G ) e. P ) )

  proof
    cP
    cV
    cmzpcl
    cfv
    wcel
    #
    cF
    cP
    wcel
    #
    cG
    cP
    wcel
    #
    w3a
    #
    @1
    @2
    vf
    cv
    #
    vg
    cv
    #
    caddc
    cof
    #
    co
    #
    cP
    wcel
    #
    @4
    @5
    cmul
    cof
    #
    co
    #
    cP
    wcel
    #
    wa
    #
    vg
    cP
    wral
    vf
    cP
    wral
    #
    cF
    cG
    @6
    co
    #
    cP
    wcel
    #
    cF
    cG
    @9
    co
    #
    cP
    wcel
    #
    wa
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    cP
    cz
    cz
    cV
    cmap
    co
    #
    cmap
    co
    wss
    #
    @19
    @4
    csn
    cxp
    cP
    wcel
    vf
    cz
    wral
    vg
    @19
    @4
    @5
    cfv
    cmpt
    cP
    wcel
    vf
    cV
    wral
    wa
    #
    @13
    @3
    @0
    @20
    @21
    @13
    wa
    wa
    #
    @0
    @1
    @2
    simp1
    #
    @3
    cV
    cvv
    wcel
    @0
    @22
    wb
    @3
    cP
    cmzpcl
    cV
    @23
    elfvexd
    vg
    cP
    vf
    vg
    vf
    vf
    cV
    elmzpcl
    syl
    mpbid
    simprrd
    @12
    @18
    cF
    @5
    @6
    co
    #
    cP
    wcel
    #
    cF
    @5
    @9
    co
    #
    cP
    wcel
    #
    wa
    vf
    vg
    cF
    cG
    cP
    cP
    @4
    cF
    wceq
    #
    @8
    @25
    @11
    @27
    @28
    @7
    @24
    cP
    @4
    cF
    @5
    @6
    oveq1
    eleq1d
    @28
    @10
    @26
    cP
    @4
    cF
    @5
    @9
    oveq1
    eleq1d
    anbi12d
    @5
    cG
    wceq
    #
    @25
    @15
    @27
    @17
    @29
    @24
    @14
    cP
    @5
    cG
    cF
    @6
    oveq2
    eleq1d
    @29
    @26
    @16
    cP
    @5
    cG
    cF
    @9
    oveq2
    eleq1d
    anbi12d
    rspc2va
    syl21anc
end
