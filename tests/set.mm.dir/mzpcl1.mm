include "cmzpcl.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "simpr.mm"
include "wss.mm"
include "cmpt.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "simpl.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "adantr.mm"
include "elmzpcl.mm"
include "syl.mm"
include "mpbid.mm"
include "simprll.mm"
include "wceq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem mzpcl1
  let cP: class P
  let cF: class F
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  let cG: class G


  assert |- ( ( P e. ( mzPolyCld ` V ) /\ F e. ZZ ) -> ( ( ZZ ^m V ) X. { F } ) e. P )

  proof
    cP
    cV
    cmzpcl
    cfv
    wcel
    #
    cF
    cz
    wcel
    #
    wa
    #
    @1
    cz
    cV
    cmap
    co
    #
    vf
    cv
    #
    csn
    #
    cxp
    #
    cP
    wcel
    #
    vf
    cz
    wral
    #
    @3
    cF
    csn
    #
    cxp
    #
    cP
    wcel
    #
    @0
    @1
    simpr
    @2
    cP
    cz
    @3
    cmap
    co
    wss
    #
    @8
    vg
    @3
    @4
    vg
    cv
    #
    cfv
    cmpt
    cP
    wcel
    vf
    cV
    wral
    #
    wa
    @4
    @13
    caddc
    cof
    co
    cP
    wcel
    @4
    @13
    cmul
    cof
    co
    cP
    wcel
    wa
    vg
    cP
    wral
    vf
    cP
    wral
    #
    wa
    wa
    #
    @8
    @2
    @0
    @16
    @0
    @1
    simpl
    @2
    cV
    cvv
    wcel
    #
    @0
    @16
    wb
    @0
    @17
    @1
    cP
    cV
    cmzpcl
    elfvex
    adantr
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
    @12
    @8
    @14
    @15
    simprll
    syl
    @7
    @11
    vf
    cF
    cz
    @4
    cF
    wceq
    #
    @6
    @10
    cP
    @18
    @5
    @9
    @3
    @4
    cF
    sneq
    xpeq2d
    eleq1d
    rspcva
    syl2anc
end
