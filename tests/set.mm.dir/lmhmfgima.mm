include "cima.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "cv.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wcel.mm"
include "clmod.mm"
include "wb.mm"
include "clmhm.mm"
include "lmhmlmod1.mm"
include "syl.mm"
include "eqid.mm"
include "islssfg2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wa.mm"
include "wss.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "lmhmlsp.mm"
include "syl2an.mm"
include "oveq2d.mm"
include "lmhmlmod2.mm"
include "adantr.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "lmhmf.mm"
include "frn.mm"
include "syl5ss.mm"
include "cres.mm"
include "wfo.mm"
include "inss2.mm"
include "adantl.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "fores.mm"
include "fofi.mm"
include "islssfgi.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "syl5eqel.mm"

theorem lmhmfgima
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume lmhmfgima.y: |- Y = ( T |`s ( F " A ) )
  assume lmhmfgima.x: |- X = ( S |`s A )
  assume lmhmfgima.u: |- U = ( LSubSp ` S )
  assume lmhmfgima.xf: |- ( ph -> X e. LFinGen )
  assume lmhmfgima.a: |- ( ph -> A e. U )
  assume lmhmfgima.f: |- ( ph -> F e. ( S LMHom T ) )


  assert |- ( ph -> Y e. LFinGen )

  proof
    wph
    cY
    cT
    cF
    cA
    cima
    #
    cress
    co
    #
    clfig
    lmhmfgima.y
    wph
    vx
    cv
    #
    cS
    clspn
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    vx
    cS
    cbs
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @1
    clfig
    wcel
    #
    wph
    cX
    clfig
    wcel
    #
    @9
    lmhmfgima.xf
    wph
    cS
    clmod
    wcel
    #
    cA
    cU
    wcel
    @11
    @9
    wb
    wph
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    @12
    lmhmfgima.f
    cS
    cT
    cF
    lmhmlmod1
    syl
    lmhmfgima.a
    @6
    cU
    cA
    @3
    cS
    cX
    vx
    lmhmfgima.x
    lmhmfgima.u
    @3
    eqid
    #
    @6
    eqid
    #
    islssfg2
    syl2anc
    mpbid
    wph
    @5
    @10
    vx
    @8
    wph
    @2
    @8
    wcel
    #
    wa
    #
    cT
    cF
    @4
    cima
    #
    cress
    co
    #
    clfig
    wcel
    @5
    @10
    @17
    @19
    cT
    cF
    @2
    cima
    #
    cT
    clspn
    cfv
    #
    cfv
    #
    cress
    co
    #
    clfig
    @17
    @18
    @22
    cT
    cress
    wph
    @13
    @2
    @6
    wss
    #
    @18
    @22
    wceq
    @16
    lmhmfgima.f
    @16
    @2
    @6
    @8
    @7
    @2
    @7
    cfn
    inss1
    sseli
    elpwid
    #
    cS
    cT
    @2
    cF
    @3
    @21
    @6
    @15
    @14
    @21
    eqid
    #
    lmhmlsp
    syl2an
    oveq2d
    @17
    cT
    clmod
    wcel
    #
    @20
    cT
    cbs
    cfv
    #
    wss
    #
    @20
    cfn
    wcel
    #
    @23
    clfig
    wcel
    wph
    @27
    @16
    wph
    @13
    @27
    lmhmfgima.f
    cS
    cT
    cF
    lmhmlmod2
    syl
    adantr
    wph
    @29
    @16
    wph
    @20
    cF
    crn
    #
    @28
    cF
    @2
    imassrn
    wph
    @6
    @28
    cF
    wf
    #
    @31
    @28
    wss
    wph
    @13
    @32
    lmhmfgima.f
    @6
    @28
    cS
    cT
    cF
    @15
    @28
    eqid
    #
    lmhmf
    syl
    #
    @6
    @28
    cF
    frn
    syl
    syl5ss
    adantr
    @17
    @2
    cfn
    wcel
    #
    @2
    @20
    cF
    @2
    cres
    #
    wfo
    #
    @30
    @16
    @35
    wph
    @8
    cfn
    @2
    @7
    cfn
    inss2
    sseli
    adantl
    @17
    cF
    wfun
    #
    @2
    cF
    cdm
    #
    wss
    @37
    wph
    @38
    @16
    wph
    @32
    @38
    @34
    @6
    @28
    cF
    ffun
    syl
    adantr
    @17
    @2
    @6
    @39
    @16
    @24
    wph
    @25
    adantl
    wph
    @39
    @6
    wceq
    #
    @16
    wph
    @32
    @40
    @34
    @6
    @28
    cF
    fdm
    syl
    adantr
    sseqtr4d
    @2
    cF
    fores
    syl2anc
    @2
    @20
    @36
    fofi
    syl2anc
    @20
    @21
    @28
    cT
    @23
    @26
    @33
    @23
    eqid
    islssfgi
    syl3anc
    eqeltrd
    @5
    @19
    @1
    clfig
    @5
    @18
    @0
    cT
    cress
    @4
    cA
    cF
    imaeq2
    oveq2d
    eleq1d
    syl5ibcom
    rexlimdva
    mpd
    syl5eqel
end
