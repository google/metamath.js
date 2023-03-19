include "cha.mm"
include "wcel.mm"
include "wf1.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ctop.mm"
include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "cuni.mm"
include "wral.mm"
include "cntop1.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cfv.mm"
include "simpl1.mm"
include "wf.mm"
include "simpl3.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "simprll.mm"
include "ffvelrnd.mm"
include "simprlr.mm"
include "simprr.mm"
include "wb.mm"
include "simpl2.mm"
include "cdm.mm"
include "fdm.mm"
include "f1dm.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "hausnei.mm"
include "syl13anc.mm"
include "ccnv.mm"
include "cima.mm"
include "simpll3.mm"
include "cnima.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simprr1.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "simprr2.mm"
include "wfun.mm"
include "ffun.mm"
include "inpreima.mm"
include "3syl.mm"
include "simprr3.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "ishaus.mm"
include "sylanbrc.mm"

theorem cnhaus
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V


  assert |- ( ( K e. Haus /\ F : X -1-1-> Y /\ F e. ( J Cn K ) ) -> J e. Haus )

  proof
    cK
    cha
    wcel
    #
    cX
    cY
    cF
    wf1
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @5
    vm
    cv
    #
    wcel
    #
    @6
    vn
    cv
    #
    wcel
    #
    @8
    @10
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    cJ
    wrex
    vm
    cJ
    wrex
    #
    wi
    #
    vy
    cJ
    cuni
    #
    wral
    vx
    @17
    wral
    cJ
    cha
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    cntop1
    3ad2ant3
    @3
    @16
    vx
    vy
    @17
    @17
    @3
    @5
    @17
    wcel
    #
    @6
    @17
    wcel
    #
    wa
    #
    @7
    @15
    @3
    @20
    @7
    wa
    #
    wa
    #
    @5
    cF
    cfv
    #
    vu
    cv
    #
    wcel
    #
    @6
    cF
    cfv
    #
    vv
    cv
    #
    wcel
    #
    @24
    @27
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vv
    cK
    wrex
    vu
    cK
    wrex
    #
    @15
    @22
    @0
    @23
    cK
    cuni
    #
    wcel
    @26
    @33
    wcel
    @23
    @26
    wne
    #
    @32
    @0
    @1
    @2
    @21
    simpl1
    @22
    @17
    @33
    @5
    cF
    @22
    @2
    @17
    @33
    cF
    wf
    #
    @0
    @1
    @2
    @21
    simpl3
    cF
    cJ
    cK
    @17
    @33
    @17
    eqid
    #
    @33
    eqid
    #
    cnf
    syl
    #
    @3
    @18
    @19
    @7
    simprll
    #
    ffvelrnd
    @22
    @17
    @33
    @6
    cF
    @38
    @3
    @18
    @19
    @7
    simprlr
    #
    ffvelrnd
    @22
    @34
    @7
    @3
    @20
    @7
    simprr
    @22
    @23
    @26
    @5
    @6
    @22
    @1
    @5
    cX
    wcel
    @6
    cX
    wcel
    @23
    @26
    wceq
    @5
    @6
    wceq
    wb
    @0
    @1
    @2
    @21
    simpl2
    #
    @22
    @5
    @17
    cX
    @39
    @22
    cF
    cdm
    #
    @17
    cX
    @22
    @35
    @42
    @17
    wceq
    @38
    @17
    @33
    cF
    fdm
    syl
    @22
    @1
    @42
    cX
    wceq
    @41
    cX
    cY
    cF
    f1dm
    syl
    eqtr3d
    #
    eleqtrd
    @22
    @6
    @17
    cX
    @40
    @43
    eleqtrd
    cX
    cY
    @5
    @6
    cF
    f1fveq
    syl12anc
    necon3bid
    mpbird
    @23
    @26
    vv
    vu
    cK
    @33
    @37
    hausnei
    syl13anc
    @22
    @31
    @15
    vu
    vv
    cK
    cK
    @22
    @24
    cK
    wcel
    #
    @27
    cK
    wcel
    #
    wa
    #
    @31
    @15
    @22
    @46
    @31
    wa
    #
    wa
    #
    cF
    ccnv
    #
    @24
    cima
    #
    cJ
    wcel
    #
    @49
    @27
    cima
    #
    cJ
    wcel
    #
    @5
    @50
    wcel
    #
    @6
    @52
    wcel
    #
    @50
    @52
    cin
    #
    c0
    wceq
    #
    @15
    @48
    @2
    @44
    @51
    @0
    @1
    @2
    @21
    @47
    simpll3
    #
    @22
    @44
    @45
    @31
    simprll
    @24
    cF
    cJ
    cK
    cnima
    syl2anc
    @48
    @2
    @45
    @53
    @58
    @22
    @44
    @45
    @31
    simprlr
    @27
    cF
    cJ
    cK
    cnima
    syl2anc
    @48
    @54
    @18
    @25
    @22
    @18
    @47
    @39
    adantr
    @25
    @28
    @30
    @46
    @22
    simprr1
    @48
    cF
    @17
    wfn
    #
    @54
    @18
    @25
    wa
    wb
    @48
    @35
    @59
    @22
    @35
    @47
    @38
    adantr
    #
    @17
    @33
    cF
    ffn
    syl
    #
    @17
    @5
    @24
    cF
    elpreima
    syl
    mpbir2and
    @48
    @55
    @19
    @28
    @22
    @19
    @47
    @40
    adantr
    @25
    @28
    @30
    @46
    @22
    simprr2
    @48
    @59
    @55
    @19
    @28
    wa
    wb
    @61
    @17
    @6
    @27
    cF
    elpreima
    syl
    mpbir2and
    @48
    @49
    @29
    cima
    #
    @56
    c0
    @48
    @35
    cF
    wfun
    @62
    @56
    wceq
    @60
    @17
    @33
    cF
    ffun
    @24
    @27
    cF
    inpreima
    3syl
    @48
    @62
    @49
    c0
    cima
    c0
    @48
    @29
    c0
    @49
    @25
    @28
    @30
    @46
    @22
    simprr3
    imaeq2d
    @49
    ima0
    syl6eq
    eqtr3d
    @14
    @54
    @55
    @57
    w3a
    @54
    @11
    @50
    @10
    cin
    #
    c0
    wceq
    #
    w3a
    vm
    vn
    @50
    @52
    cJ
    cJ
    @8
    @50
    wceq
    #
    @9
    @54
    @13
    @64
    @11
    @8
    @50
    @5
    eleq2
    @65
    @12
    @63
    c0
    @8
    @50
    @10
    ineq1
    eqeq1d
    3anbi13d
    @10
    @52
    wceq
    #
    @11
    @55
    @64
    @57
    @54
    @10
    @52
    @6
    eleq2
    @66
    @63
    @56
    c0
    @10
    @52
    @50
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    expr
    rexlimdvva
    mpd
    expr
    ralrimivva
    vx
    vy
    vn
    vm
    cJ
    @17
    @36
    ishaus
    sylanbrc
end
