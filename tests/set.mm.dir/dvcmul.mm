include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "cfv.mm"
include "caddc.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "wf.mm"
include "fconst6g.mm"
include "syl.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cdm.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "dvbss.mm"
include "sseldd.mm"
include "wceq.mm"
include "cres.mm"
include "dvconst.mm"
include "dmeqd.mm"
include "c0ex.mm"
include "fconst.mm"
include "fdmi.mm"
include "syl6eq.mm"
include "sseqtr4d.mm"
include "dvres3.mm"
include "syl22anc.mm"
include "xpssres.mm"
include "oveq2d.mm"
include "reseq1d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "fconst2.mm"
include "sylibr.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "dvmul.mm"
include "fveq1d.mm"
include "fvconst2.mm"
include "oveq1d.mm"
include "ffvelrnd.mm"
include "mul02d.mm"
include "fvconst2g.mm"
include "syl2anc.mm"
include "dvfg.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "addid2d.mm"
include "3eqtrd.mm"

theorem dvcmul
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let cF: class F
  let cX: class X
  let vx: setvar x
  assume dvcmul.s: |- ( ph -> S e. { RR , CC } )
  assume dvcmul.f: |- ( ph -> F : X --> CC )
  assume dvcmul.a: |- ( ph -> A e. CC )
  assume dvcmul.x: |- ( ph -> X C_ S )
  assume dvcmul.c: |- ( ph -> C e. dom ( S _D F ) )


  assert |- ( ph -> ( ( S _D ( ( S X. { A } ) oF x. F ) ) ` C ) = ( A x. ( ( S _D F ) ` C ) ) )

  proof
    wph
    cC
    cS
    cS
    cA
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    co
    cdv
    co
    cfv
    cC
    cS
    @1
    cdv
    co
    #
    cfv
    #
    cC
    cF
    cfv
    #
    cmul
    co
    #
    cC
    cS
    cF
    cdv
    co
    #
    cfv
    #
    cC
    @1
    cfv
    #
    cmul
    co
    #
    caddc
    co
    cc0
    cA
    @7
    cmul
    co
    #
    caddc
    co
    @10
    wph
    cC
    cS
    @1
    cF
    cS
    cX
    wph
    cA
    cc
    wcel
    #
    cS
    cc
    @1
    wf
    dvcmul.a
    cS
    cA
    cc
    fconst6g
    syl
    cS
    cS
    wss
    wph
    cS
    ssid
    a1i
    dvcmul.f
    dvcmul.x
    dvcmul.s
    wph
    cC
    cS
    @2
    cdm
    #
    wph
    cX
    cS
    cC
    dvcmul.x
    wph
    @6
    cdm
    #
    cX
    cC
    wph
    cX
    cS
    cF
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    cS
    cc
    wss
    #
    dvcmul.s
    cS
    recnprss
    syl
    #
    dvcmul.f
    dvcmul.x
    dvbss
    dvcmul.c
    sseldd
    #
    sseldd
    #
    wph
    cS
    cc0
    csn
    #
    @2
    wf
    #
    @12
    cS
    wceq
    wph
    @2
    cS
    @19
    cxp
    #
    wceq
    @20
    wph
    cS
    cc
    @0
    cxp
    #
    cS
    cres
    #
    cdv
    co
    #
    cc
    @22
    cdv
    co
    #
    cS
    cres
    #
    @2
    @21
    wph
    @14
    cc
    cc
    @22
    wf
    #
    cc
    cc
    wss
    #
    cS
    @25
    cdm
    #
    wss
    @24
    @26
    wceq
    dvcmul.s
    wph
    @11
    @27
    dvcmul.a
    cc
    cA
    cc
    fconst6g
    syl
    @28
    wph
    cc
    ssid
    a1i
    wph
    cS
    cc
    @29
    @16
    wph
    @29
    cc
    @19
    cxp
    #
    cdm
    cc
    wph
    @25
    @30
    wph
    @11
    @25
    @30
    wceq
    dvcmul.a
    cA
    dvconst
    syl
    #
    dmeqd
    cc
    @19
    @30
    cc
    cc0
    c0ex
    fconst
    fdmi
    syl6eq
    sseqtr4d
    cc
    cS
    @22
    dvres3
    syl22anc
    wph
    @23
    @1
    cS
    cdv
    wph
    @15
    @23
    @1
    wceq
    @16
    cc
    @0
    cS
    xpssres
    syl
    oveq2d
    wph
    @26
    @30
    cS
    cres
    #
    @21
    wph
    @25
    @30
    cS
    @31
    reseq1d
    wph
    @15
    @32
    @21
    wceq
    @16
    cc
    @19
    cS
    xpssres
    syl
    eqtrd
    3eqtr3d
    #
    cS
    cc0
    @2
    c0ex
    fconst2
    sylibr
    cS
    @19
    @2
    fdm
    syl
    eleqtrrd
    dvcmul.c
    dvmul
    wph
    @5
    cc0
    @9
    @10
    caddc
    wph
    @5
    cc0
    @4
    cmul
    co
    cc0
    wph
    @3
    cc0
    @4
    cmul
    wph
    @3
    cC
    @21
    cfv
    #
    cc0
    wph
    cC
    @2
    @21
    @33
    fveq1d
    wph
    cC
    cS
    wcel
    #
    @34
    cc0
    wceq
    @18
    cS
    cc0
    cC
    c0ex
    fvconst2
    syl
    eqtrd
    oveq1d
    wph
    @4
    wph
    cX
    cc
    cC
    cF
    dvcmul.f
    @17
    ffvelrnd
    mul02d
    eqtrd
    wph
    @9
    @7
    cA
    cmul
    co
    @10
    wph
    @8
    cA
    @7
    cmul
    wph
    @11
    @35
    @8
    cA
    wceq
    dvcmul.a
    @18
    cS
    cA
    cC
    cc
    fvconst2g
    syl2anc
    oveq2d
    wph
    @7
    cA
    wph
    @13
    cc
    cC
    @6
    wph
    @14
    @13
    cc
    @6
    wf
    dvcmul.s
    cS
    cF
    dvfg
    syl
    dvcmul.c
    ffvelrnd
    #
    dvcmul.a
    mulcomd
    eqtrd
    oveq12d
    wph
    @10
    wph
    cA
    @7
    dvcmul.a
    @36
    mulcld
    addid2d
    3eqtrd
end
