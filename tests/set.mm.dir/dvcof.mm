include "cv.mm"
include "ccom.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmul.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "cdm.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "cr.mm"
include "cpr.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "eleqtrrd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "dvco.mm"
include "mpteq2dva.mm"
include "dvfg.mm"
include "syl.mm"
include "recnprss.mm"
include "fco.mm"
include "syl2anc.mm"
include "dvbss.mm"
include "wbr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cvv.mm"
include "fvexd.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "4syl.mm"
include "mpbid.mm"
include "eqid.mm"
include "dvcobr.mm"
include "reldv.mm"
include "releldmi.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "feqmptd.mm"
include "ssexd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem dvcof
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume dvcof.s: |- ( ph -> S e. { RR , CC } )
  assume dvcof.t: |- ( ph -> T e. { RR , CC } )
  assume dvcof.f: |- ( ph -> F : X --> CC )
  assume dvcof.g: |- ( ph -> G : Y --> X )
  assume dvcof.df: |- ( ph -> dom ( S _D F ) = X )
  assume dvcof.dg: |- ( ph -> dom ( T _D G ) = Y )


  assert |- ( ph -> ( T _D ( F o. G ) ) = ( ( ( S _D F ) o. G ) oF x. ( T _D G ) ) )

  proof
    wph
    vx
    cY
    vx
    cv
    #
    cT
    cF
    cG
    ccom
    #
    cdv
    co
    #
    cfv
    #
    cmpt
    vx
    cY
    @0
    cG
    cfv
    #
    cS
    cF
    cdv
    co
    #
    cfv
    #
    @0
    cT
    cG
    cdv
    co
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    @2
    @5
    cG
    ccom
    #
    @7
    cmul
    cof
    co
    wph
    vx
    cY
    @3
    @9
    wph
    @0
    cY
    wcel
    #
    wa
    #
    @0
    cS
    cT
    cF
    cG
    cX
    cY
    wph
    cX
    cc
    cF
    wf
    #
    @11
    dvcof.f
    adantr
    #
    wph
    cX
    cS
    wss
    @11
    wph
    cX
    @5
    cdm
    #
    cS
    dvcof.df
    cS
    cF
    dvbsss
    syl6eqssr
    adantr
    #
    wph
    cY
    cX
    cG
    wf
    #
    @11
    dvcof.g
    adantr
    #
    wph
    cY
    cT
    wss
    @11
    wph
    cY
    @7
    cdm
    #
    cT
    dvcof.dg
    cT
    cG
    dvbsss
    syl6eqssr
    #
    adantr
    #
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    @11
    dvcof.s
    adantr
    #
    wph
    cT
    @22
    wcel
    #
    @11
    dvcof.t
    adantr
    #
    @12
    @4
    cX
    @15
    wph
    cY
    cX
    @0
    cG
    dvcof.g
    ffvelrnda
    #
    wph
    @15
    cX
    wceq
    @11
    dvcof.df
    adantr
    eleqtrrd
    #
    wph
    @0
    @19
    wcel
    #
    @11
    wph
    @19
    cY
    @0
    dvcof.dg
    eleq2d
    biimpar
    #
    dvco
    mpteq2dva
    wph
    vx
    cY
    cc
    @2
    wph
    @2
    cdm
    #
    cc
    @2
    wf
    #
    cY
    cc
    @2
    wf
    wph
    @25
    @32
    dvcof.t
    cT
    @1
    dvfg
    syl
    wph
    @31
    cY
    cc
    @2
    wph
    @31
    cY
    wph
    cY
    cT
    @1
    wph
    @25
    cT
    cc
    wss
    #
    dvcof.t
    cT
    recnprss
    #
    syl
    wph
    @13
    @17
    cY
    cc
    @1
    wf
    dvcof.f
    dvcof.g
    cY
    cX
    cc
    cF
    cG
    fco
    syl2anc
    @20
    dvbss
    wph
    vx
    cY
    @31
    wph
    @11
    @0
    @31
    wcel
    #
    @12
    @0
    @9
    @2
    wbr
    @35
    @12
    @0
    cS
    cT
    cF
    cG
    ccnfld
    ctopn
    cfv
    #
    @6
    @8
    cvv
    cX
    cY
    @14
    @16
    @18
    @21
    @12
    @23
    cS
    cc
    wss
    @24
    cS
    recnprss
    syl
    @12
    @25
    @33
    @26
    @34
    syl
    @12
    @4
    @5
    fvexd
    #
    @12
    @0
    @7
    fvexd
    #
    @12
    @4
    @15
    wcel
    #
    @4
    @6
    @5
    wbr
    #
    @28
    @12
    @23
    @15
    cc
    @5
    wf
    #
    @5
    wfun
    @39
    @40
    wb
    @24
    cS
    cF
    dvfg
    #
    @15
    cc
    @5
    ffun
    @4
    @5
    funfvbrb
    4syl
    mpbid
    @12
    @29
    @0
    @8
    @7
    wbr
    #
    @30
    @12
    @25
    @19
    cc
    @7
    wf
    #
    @7
    wfun
    @29
    @43
    wb
    @26
    cT
    cG
    dvfg
    #
    @19
    cc
    @7
    ffun
    @0
    @7
    funfvbrb
    4syl
    mpbid
    @36
    eqid
    dvcobr
    @0
    @9
    @2
    cT
    @1
    reldv
    releldmi
    syl
    ex
    ssrdv
    eqssd
    feq2d
    mpbid
    feqmptd
    wph
    vx
    cY
    @6
    @8
    cmul
    @10
    @7
    cvv
    cvv
    cvv
    wph
    cY
    cT
    @22
    dvcof.t
    @20
    ssexd
    @37
    @38
    wph
    vx
    vy
    cY
    cX
    @4
    vy
    cv
    #
    @5
    cfv
    @6
    cG
    @5
    @27
    wph
    vx
    cY
    cX
    cG
    dvcof.g
    feqmptd
    wph
    vy
    cX
    cc
    @5
    wph
    @41
    cX
    cc
    @5
    wf
    wph
    @23
    @41
    dvcof.s
    @42
    syl
    wph
    @15
    cX
    cc
    @5
    dvcof.df
    feq2d
    mpbid
    feqmptd
    @46
    @4
    @5
    fveq2
    fmptco
    wph
    vx
    cY
    cc
    @7
    wph
    @44
    cY
    cc
    @7
    wf
    wph
    @25
    @44
    dvcof.t
    @45
    syl
    wph
    @19
    cY
    cc
    @7
    dvcof.dg
    feq2d
    mpbid
    feqmptd
    offval2
    3eqtr4d
end
