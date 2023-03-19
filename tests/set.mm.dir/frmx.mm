include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cn0.mm"
include "cz.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmul.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wcel.mm"
include "wral.mm"
include "cuz.mm"
include "crmx.mm"
include "wf.mm"
include "wa.mm"
include "rmxyelxp.mm"
include "xp1st.mm"
include "syl.mm"
include "rgen2.mm"
include "df-rmx.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem frmx
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- rmX : ( ( ZZ>= ` 2 ) X. ZZ ) --> NN0

  proof
    va
    cv
    #
    @0
    c2
    cexp
    co
    c1
    cmin
    co
    csqrt
    cfv
    #
    caddc
    co
    vb
    cv
    #
    cexp
    co
    vc
    cn0
    cz
    cxp
    #
    vc
    cv
    #
    c1st
    cfv
    @1
    @4
    c2nd
    cfv
    cmul
    co
    caddc
    co
    cmpt
    ccnv
    cfv
    #
    c1st
    cfv
    #
    cn0
    wcel
    #
    vb
    cz
    wral
    va
    c2
    cuz
    cfv
    #
    wral
    @8
    cz
    cxp
    cn0
    crmx
    wf
    @7
    va
    vb
    @8
    cz
    @0
    @8
    wcel
    @2
    cz
    wcel
    wa
    @5
    @3
    wcel
    @7
    @0
    @2
    vc
    rmxyelxp
    @5
    cn0
    cz
    xp1st
    syl
    rgen2
    va
    vb
    @8
    cz
    @6
    cn0
    crmx
    vb
    va
    vc
    df-rmx
    fmpt2
    mpbi
end
