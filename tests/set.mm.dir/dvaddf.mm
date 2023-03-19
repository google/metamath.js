include "cdv.mm"
include "co.mm"
include "caddc.mm"
include "cof.mm"
include "cv.mm"
include "cfv.mm"
include "cvv.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "cdm.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "ssexd.mm"
include "wf.mm"
include "wfn.mm"
include "wcel.mm"
include "dvfg.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffn.mm"
include "wss.mm"
include "recnprss.mm"
include "wa.mm"
include "addcl.mm"
include "adantl.mm"
include "inidm.mm"
include "off.mm"
include "dvbss.mm"
include "wbr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "adantr.mm"
include "fvexd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "4syl.mm"
include "eqid.mm"
include "dvaddbr.mm"
include "reldv.mm"
include "releldmi.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "eqidd.mm"
include "dvadd.mm"
include "eqcomd.mm"
include "offveq.mm"

theorem dvaddf
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


  assert |- ( ph -> ( S _D ( F oF + G ) ) = ( ( S _D F ) oF + ( S _D G ) ) )

  proof
    wph
    cS
    cF
    cdv
    co
    #
    cS
    cG
    cdv
    co
    #
    caddc
    cof
    #
    co
    cS
    cF
    cG
    @2
    co
    #
    cdv
    co
    #
    wph
    vx
    cX
    vx
    cv
    #
    @0
    cfv
    #
    @5
    @1
    cfv
    #
    caddc
    @0
    @1
    @4
    cvv
    wph
    cX
    cS
    cr
    cc
    cpr
    #
    dvaddf.s
    wph
    cX
    @0
    cdm
    #
    cS
    dvaddf.df
    cS
    cF
    dvbsss
    syl6eqssr
    #
    ssexd
    #
    wph
    cX
    cc
    @0
    wf
    #
    @0
    cX
    wfn
    wph
    @9
    cc
    @0
    wf
    #
    @12
    wph
    cS
    @8
    wcel
    #
    @13
    dvaddf.s
    cS
    cF
    dvfg
    #
    syl
    wph
    @9
    cX
    cc
    @0
    dvaddf.df
    feq2d
    mpbid
    cX
    cc
    @0
    ffn
    syl
    wph
    cX
    cc
    @1
    wf
    #
    @1
    cX
    wfn
    wph
    @1
    cdm
    #
    cc
    @1
    wf
    #
    @16
    wph
    @14
    @18
    dvaddf.s
    cS
    cG
    dvfg
    #
    syl
    wph
    @17
    cX
    cc
    @1
    dvaddf.dg
    feq2d
    mpbid
    cX
    cc
    @1
    ffn
    syl
    wph
    cX
    cc
    @4
    wf
    #
    @4
    cX
    wfn
    wph
    @4
    cdm
    #
    cc
    @4
    wf
    #
    @20
    wph
    @14
    @22
    dvaddf.s
    cS
    @3
    dvfg
    syl
    wph
    @21
    cX
    cc
    @4
    wph
    @21
    cX
    wph
    cX
    cS
    @3
    wph
    @14
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
    caddc
    cc
    cc
    cc
    cF
    cG
    cvv
    cvv
    @5
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @5
    @25
    caddc
    co
    cc
    wcel
    wph
    @5
    @25
    addcl
    adantl
    dvaddf.f
    dvaddf.g
    @11
    @11
    cX
    inidm
    off
    @10
    dvbss
    wph
    vx
    cX
    @21
    wph
    @5
    cX
    wcel
    #
    @5
    @21
    wcel
    #
    wph
    @26
    wa
    #
    @5
    @6
    @7
    caddc
    co
    #
    @4
    wbr
    @27
    @28
    @5
    cS
    cF
    cG
    ccnfld
    ctopn
    cfv
    #
    @6
    @7
    cvv
    cX
    cX
    wph
    cX
    cc
    cF
    wf
    @26
    dvaddf.f
    adantr
    #
    wph
    cX
    cS
    wss
    @26
    @10
    adantr
    #
    wph
    cX
    cc
    cG
    wf
    @26
    dvaddf.g
    adantr
    #
    @32
    wph
    @23
    @26
    @24
    adantr
    @28
    @5
    @0
    fvexd
    @28
    @5
    @1
    fvexd
    @28
    @5
    @9
    wcel
    #
    @5
    @6
    @0
    wbr
    #
    wph
    @34
    @26
    wph
    @9
    cX
    @5
    dvaddf.df
    eleq2d
    biimpar
    #
    @28
    @14
    @13
    @0
    wfun
    @34
    @35
    wb
    wph
    @14
    @26
    dvaddf.s
    adantr
    #
    @15
    @9
    cc
    @0
    ffun
    @5
    @0
    funfvbrb
    4syl
    mpbid
    @28
    @5
    @17
    wcel
    #
    @5
    @7
    @1
    wbr
    #
    wph
    @38
    @26
    wph
    @17
    cX
    @5
    dvaddf.dg
    eleq2d
    biimpar
    #
    @28
    @14
    @18
    @1
    wfun
    @38
    @39
    wb
    @37
    @19
    @17
    cc
    @1
    ffun
    @5
    @1
    funfvbrb
    4syl
    mpbid
    @30
    eqid
    dvaddbr
    @5
    @29
    @4
    cS
    @3
    reldv
    releldmi
    syl
    ex
    ssrdv
    eqssd
    feq2d
    mpbid
    cX
    cc
    @4
    ffn
    syl
    @28
    @6
    eqidd
    @28
    @7
    eqidd
    @28
    @5
    @4
    cfv
    @29
    @28
    @5
    cS
    cF
    cG
    cX
    cX
    @31
    @32
    @33
    @32
    @37
    @36
    @40
    dvadd
    eqcomd
    offveq
    eqcomd
end
