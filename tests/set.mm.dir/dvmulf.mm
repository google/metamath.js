include "cv.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "cfv.mm"
include "cmpt.mm"
include "caddc.mm"
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
include "eleq2d.mm"
include "biimpar.mm"
include "dvmul.mm"
include "mpteq2dva.mm"
include "dvfg.mm"
include "syl.mm"
include "recnprss.mm"
include "cvv.mm"
include "mulcl.mm"
include "adantl.mm"
include "ssexd.mm"
include "inidm.mm"
include "off.mm"
include "dvbss.mm"
include "wbr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "fvexd.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "3syl.mm"
include "mpbid.mm"
include "eqid.mm"
include "dvmulbr.mm"
include "reldv.mm"
include "releldmi.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "feqmptd.mm"
include "ovexd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem dvmulf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dvaddf.s: |- ( ph -> S e. { RR , CC } )
  assume dvaddf.f: |- ( ph -> F : X --> CC )
  assume dvaddf.g: |- ( ph -> G : X --> CC )
  assume dvaddf.df: |- ( ph -> dom ( S _D F ) = X )
  assume dvaddf.dg: |- ( ph -> dom ( S _D G ) = X )


  assert |- ( ph -> ( S _D ( F oF x. G ) ) = ( ( ( S _D F ) oF x. G ) oF + ( ( S _D G ) oF x. F ) ) )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    cS
    cF
    cG
    cmul
    cof
    #
    co
    #
    cdv
    co
    #
    cfv
    #
    cmpt
    vx
    cX
    @0
    cS
    cF
    cdv
    co
    #
    cfv
    #
    @0
    cG
    cfv
    #
    cmul
    co
    #
    @0
    cS
    cG
    cdv
    co
    #
    cfv
    #
    @0
    cF
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @3
    @5
    cG
    @1
    co
    #
    @9
    cF
    @1
    co
    #
    caddc
    cof
    co
    wph
    vx
    cX
    @4
    @13
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @0
    cS
    cF
    cG
    cX
    cX
    wph
    cX
    cc
    cF
    wf
    @16
    dvaddf.f
    adantr
    #
    wph
    cX
    cS
    wss
    @16
    wph
    cX
    @5
    cdm
    #
    cS
    dvaddf.df
    cS
    cF
    dvbsss
    syl6eqssr
    #
    adantr
    #
    wph
    cX
    cc
    cG
    wf
    @16
    dvaddf.g
    adantr
    #
    @21
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    @16
    dvaddf.s
    adantr
    wph
    @0
    @19
    wcel
    #
    @16
    wph
    @19
    cX
    @0
    dvaddf.df
    eleq2d
    biimpar
    #
    wph
    @0
    @9
    cdm
    #
    wcel
    #
    @16
    wph
    @27
    cX
    @0
    dvaddf.dg
    eleq2d
    biimpar
    #
    dvmul
    mpteq2dva
    wph
    vx
    cX
    cc
    @3
    wph
    @3
    cdm
    #
    cc
    @3
    wf
    #
    cX
    cc
    @3
    wf
    wph
    @24
    @31
    dvaddf.s
    cS
    @2
    dvfg
    syl
    wph
    @30
    cX
    cc
    @3
    wph
    @30
    cX
    wph
    cX
    cS
    @2
    wph
    @24
    cS
    cc
    wss
    #
    dvaddf.s
    cS
    recnprss
    syl
    #
    wph
    vx
    vy
    cX
    cX
    cX
    cmul
    cc
    cc
    cc
    cF
    cG
    cvv
    cvv
    @0
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @0
    @34
    cmul
    co
    cc
    wcel
    wph
    @0
    @34
    mulcl
    adantl
    dvaddf.f
    dvaddf.g
    wph
    cX
    cS
    @23
    dvaddf.s
    @20
    ssexd
    #
    @35
    cX
    inidm
    off
    @20
    dvbss
    wph
    vx
    cX
    @30
    wph
    @16
    @0
    @30
    wcel
    #
    @17
    @0
    @13
    @3
    wbr
    @36
    @17
    @0
    cS
    cF
    cG
    ccnfld
    ctopn
    cfv
    #
    @6
    @10
    cvv
    cX
    cX
    @18
    @21
    @22
    @21
    wph
    @32
    @16
    @33
    adantr
    @17
    @0
    @5
    fvexd
    #
    @17
    @0
    @9
    fvexd
    #
    @17
    @25
    @0
    @6
    @5
    wbr
    #
    @26
    @17
    @19
    cc
    @5
    wf
    #
    @5
    wfun
    @25
    @40
    wb
    wph
    @41
    @16
    wph
    @24
    @41
    dvaddf.s
    cS
    cF
    dvfg
    syl
    #
    adantr
    @19
    cc
    @5
    ffun
    @0
    @5
    funfvbrb
    3syl
    mpbid
    @17
    @28
    @0
    @10
    @9
    wbr
    #
    @29
    @17
    @27
    cc
    @9
    wf
    #
    @9
    wfun
    @28
    @43
    wb
    wph
    @44
    @16
    wph
    @24
    @44
    dvaddf.s
    cS
    cG
    dvfg
    syl
    #
    adantr
    @27
    cc
    @9
    ffun
    @0
    @9
    funfvbrb
    3syl
    mpbid
    @37
    eqid
    dvmulbr
    @0
    @13
    @3
    cS
    @2
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
    cX
    @8
    @12
    caddc
    @14
    @15
    cvv
    cvv
    cvv
    @35
    @17
    @6
    @7
    cmul
    ovexd
    @17
    @10
    @11
    cmul
    ovexd
    wph
    vx
    cX
    @6
    @7
    cmul
    @5
    cG
    cvv
    cvv
    cvv
    @35
    @38
    @17
    @0
    cG
    fvexd
    wph
    vx
    cX
    cc
    @5
    wph
    @41
    cX
    cc
    @5
    wf
    @42
    wph
    @19
    cX
    cc
    @5
    dvaddf.df
    feq2d
    mpbid
    feqmptd
    wph
    vx
    cX
    cc
    cG
    dvaddf.g
    feqmptd
    offval2
    wph
    vx
    cX
    @10
    @11
    cmul
    @9
    cF
    cvv
    cvv
    cvv
    @35
    @39
    @17
    @0
    cF
    fvexd
    wph
    vx
    cX
    cc
    @9
    wph
    @44
    cX
    cc
    @9
    wf
    @45
    wph
    @27
    cX
    cc
    @9
    dvaddf.dg
    feq2d
    mpbid
    feqmptd
    wph
    vx
    cX
    cc
    cF
    dvaddf.f
    feqmptd
    offval2
    offval2
    3eqtr4d
end
