include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "cfil.mm"
include "cfv.mm"
include "crn.mm"
include "cin.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "cfm.mm"
include "co.mm"
include "wf.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "foima.mm"
include "3syl.mm"
include "cfbas.mm"
include "cfg.mm"
include "filtop.mm"
include "syl.mm"
include "fgcl.mm"
include "eqid.mm"
include "imaelfm.mm"
include "syl31anc.mm"
include "eqeltrrd.mm"
include "sseldd.mm"
include "filin.mm"
include "syl3anc.mm"
include "simprr.mm"
include "elin.mm"
include "wrex.mm"
include "wb.mm"
include "fvelrnb.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "syl2anc.mm"
include "cnvimass.mm"
include "funfvima2.mm"
include "sylancl.mm"
include "ssel.mm"
include "ad2antrl.mm"
include "syld.mm"
include "sylbid.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibcom.mm"
include "expr.mm"
include "rexlimdv.mm"
include "com23.mm"
include "impd.mm"
include "adantrr.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "filss.mm"
include "syl13anc.mm"
include "exp32.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"

theorem fmfnfmlem2
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cB: class B
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vf: setvar f
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume fmfnfm.b: |- ( ph -> B e. ( fBas ` Y ) )
  assume fmfnfm.l: |- ( ph -> L e. ( Fil ` X ) )
  assume fmfnfm.f: |- ( ph -> F : Y --> X )
  assume fmfnfm.fm: |- ( ph -> ( ( X FilMap F ) ` B ) C_ L )

  disjoint s t
  disjoint s x
  disjoint B s
  disjoint t x
  disjoint B t
  disjoint B x
  disjoint F s
  disjoint F t
  disjoint F x
  disjoint L s
  disjoint L t
  disjoint L x
  disjoint ph s
  disjoint ph t
  disjoint ph x
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L f
  disjoint L w
  disjoint L y
  disjoint L z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint X f
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> ( E. x e. L s = ( `' F " x ) -> ( ( F " s ) C_ t -> ( t C_ X -> t e. L ) ) ) )

  proof
    wph
    vs
    cv
    #
    cF
    ccnv
    vx
    cv
    #
    cima
    #
    wceq
    #
    cF
    @0
    cima
    #
    vt
    cv
    #
    wss
    #
    @5
    cX
    wss
    #
    @5
    cL
    wcel
    #
    wi
    #
    wi
    #
    vx
    cL
    wph
    @1
    cL
    wcel
    #
    wa
    #
    @10
    @3
    cF
    @2
    cima
    #
    @5
    wss
    #
    @9
    wi
    @12
    @14
    @7
    @8
    @12
    @14
    @7
    wa
    #
    wa
    #
    cL
    cX
    cfil
    cfv
    wcel
    #
    @1
    cF
    crn
    #
    cin
    #
    cL
    wcel
    #
    @7
    @19
    @5
    wss
    @8
    wph
    @17
    @11
    @15
    fmfnfm.l
    ad2antrr
    #
    @16
    @17
    @11
    @18
    cL
    wcel
    #
    @20
    @21
    wph
    @11
    @15
    simplr
    wph
    @22
    @11
    @15
    wph
    cB
    cX
    cF
    cfm
    co
    cfv
    #
    cL
    @18
    fmfnfm.fm
    wph
    cF
    cY
    cima
    #
    @18
    @23
    wph
    cY
    cX
    cF
    wf
    #
    cY
    @18
    cF
    wfo
    #
    @24
    @18
    wceq
    fmfnfm.f
    @25
    cF
    cY
    wfn
    #
    @26
    cY
    cX
    cF
    ffn
    #
    cY
    cF
    dffn4
    sylib
    cY
    @18
    cF
    foima
    3syl
    wph
    cX
    cL
    wcel
    #
    cB
    cY
    cfbas
    cfv
    wcel
    #
    @25
    cY
    cY
    cB
    cfg
    co
    #
    wcel
    #
    @24
    @23
    wcel
    wph
    @17
    @29
    fmfnfm.l
    cL
    cX
    filtop
    syl
    fmfnfm.b
    fmfnfm.f
    wph
    @30
    @31
    cY
    cfil
    cfv
    wcel
    @32
    fmfnfm.b
    cB
    cY
    fgcl
    @31
    cY
    filtop
    3syl
    cL
    cB
    cY
    cF
    @31
    cX
    cY
    @31
    eqid
    imaelfm
    syl31anc
    eqeltrrd
    sseldd
    ad2antrr
    @1
    @18
    cL
    cX
    filin
    syl3anc
    @12
    @14
    @7
    simprr
    @16
    vy
    @19
    @5
    vy
    cv
    #
    @19
    wcel
    @33
    @1
    wcel
    #
    @33
    @18
    wcel
    #
    wa
    #
    @16
    @33
    @5
    wcel
    #
    @33
    @1
    @18
    elin
    @12
    @14
    @36
    @37
    wi
    @7
    @12
    @14
    wa
    #
    @34
    @35
    @37
    @38
    @35
    @34
    @37
    @38
    @35
    vz
    cv
    #
    cF
    cfv
    #
    @33
    wceq
    #
    vz
    cY
    wrex
    #
    @34
    @37
    wi
    #
    wph
    @35
    @42
    wb
    #
    @11
    @14
    wph
    @25
    @27
    @44
    fmfnfm.f
    @28
    vz
    cY
    @33
    cF
    fvelrnb
    3syl
    ad2antrr
    @38
    @41
    @43
    vz
    cY
    @12
    @14
    @39
    cY
    wcel
    #
    @41
    @43
    wi
    @12
    @14
    @45
    wa
    #
    wa
    #
    @40
    @1
    wcel
    #
    @40
    @5
    wcel
    #
    wi
    @41
    @43
    @47
    @48
    @39
    @2
    wcel
    #
    @49
    @47
    cF
    wfun
    #
    @39
    cF
    cdm
    #
    wcel
    @48
    @50
    wb
    wph
    @51
    @11
    @46
    wph
    @25
    @51
    fmfnfm.f
    cY
    cX
    cF
    ffun
    syl
    ad2antrr
    #
    @47
    @39
    cY
    @52
    @12
    @14
    @45
    simprr
    wph
    @52
    cY
    wceq
    #
    @11
    @46
    wph
    @25
    @54
    fmfnfm.f
    cY
    cX
    cF
    fdm
    syl
    ad2antrr
    eleqtrrd
    @39
    @1
    cF
    fvimacnv
    syl2anc
    @47
    @50
    @40
    @13
    wcel
    #
    @49
    @47
    @51
    @2
    @52
    wss
    @50
    @55
    wi
    @53
    cF
    @1
    cnvimass
    @2
    @39
    cF
    funfvima2
    sylancl
    @14
    @55
    @49
    wi
    @12
    @45
    @13
    @5
    @40
    ssel
    ad2antrl
    syld
    sylbid
    @41
    @48
    @34
    @49
    @37
    @40
    @33
    @1
    eleq1
    @40
    @33
    @5
    eleq1
    imbi12d
    syl5ibcom
    expr
    rexlimdv
    sylbid
    com23
    impd
    adantrr
    syl5bi
    ssrdv
    @19
    @5
    cL
    cX
    filss
    syl13anc
    exp32
    @3
    @6
    @14
    @9
    @3
    @4
    @13
    @5
    @0
    @2
    cF
    imaeq2
    sseq1d
    imbi1d
    syl5ibrcom
    rexlimdva
end
