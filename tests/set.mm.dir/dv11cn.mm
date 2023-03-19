include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cvv.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "wcel.mm"
include "cabs.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "inidm.mm"
include "offn.mm"
include "0cn.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "cv.mm"
include "wa.mm"
include "subcl.mm"
include "adantl.mm"
include "off.mm"
include "ffvelrnda.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "simpr.mm"
include "adantr.mm"
include "jca.mm"
include "cxmt.mm"
include "cxr.mm"
include "wss.mm"
include "cnxmet.mm"
include "blssm.mm"
include "syl3anc.mm"
include "syl5eqss.mm"
include "cdv.mm"
include "cdm.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "offval2.mm"
include "oveq2d.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "fvexd.mm"
include "dvfcn.mm"
include "feq2d.mm"
include "mpbii.mm"
include "eqtr3d.mm"
include "3eqtr3rd.mm"
include "dvmptsub.mm"
include "subidd.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"
include "dmeqd.mm"
include "c0.mm"
include "wne.mm"
include "snnzg.mm"
include "dmxp.mm"
include "mp2b.mm"
include "syl6eq.mm"
include "eqimss2.mm"
include "0red.mm"
include "fveq1d.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "sylan9eq.mm"
include "abs00bd.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "dvlipcn.mm"
include "syldan.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "fvmpt.mm"
include "ffvelrnd.mm"
include "subeq0bd.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "sselda.mm"
include "sseldd.mm"
include "subcld.mm"
include "abscld.mm"
include "recnd.mm"
include "mul02d.mm"
include "3brtr3d.mm"
include "absge0d.mm"
include "wb.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "abs00d.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"
include "ofsubeq0.mm"
include "mpbid.mm"

theorem dv11cn
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dv11cn.x: |- X = ( A ( ball ` ( abs o. - ) ) R )
  assume dv11cn.a: |- ( ph -> A e. CC )
  assume dv11cn.r: |- ( ph -> R e. RR* )
  assume dv11cn.f: |- ( ph -> F : X --> CC )
  assume dv11cn.g: |- ( ph -> G : X --> CC )
  assume dv11cn.d: |- ( ph -> dom ( CC _D F ) = X )
  assume dv11cn.e: |- ( ph -> ( CC _D F ) = ( CC _D G ) )
  assume dv11cn.c: |- ( ph -> C e. X )
  assume dv11cn.p: |- ( ph -> ( F ` C ) = ( G ` C ) )


  assert |- ( ph -> F = G )

  proof
    wph
    cF
    cG
    cmin
    cof
    co
    #
    cX
    cc0
    csn
    #
    cxp
    #
    wceq
    #
    cF
    cG
    wceq
    #
    wph
    vx
    cX
    @0
    @2
    wph
    cX
    cX
    cmin
    cX
    cF
    cG
    cvv
    cvv
    wph
    cX
    cc
    cF
    wf
    #
    cF
    cX
    wfn
    dv11cn.f
    cX
    cc
    cF
    ffn
    syl
    wph
    cX
    cc
    cG
    wf
    #
    cG
    cX
    wfn
    dv11cn.g
    cX
    cc
    cG
    ffn
    syl
    cX
    cvv
    wcel
    #
    wph
    cX
    cA
    cR
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    cvv
    dv11cn.x
    cA
    cR
    @9
    ovex
    eqeltri
    a1i
    #
    @11
    cX
    inidm
    #
    offn
    cc0
    cc
    wcel
    #
    @2
    cX
    wfn
    wph
    0cn
    cX
    cc0
    cc
    fnconstg
    mp1i
    wph
    vx
    cv
    #
    cX
    wcel
    #
    wa
    #
    @14
    @0
    cfv
    #
    cc0
    @14
    @2
    cfv
    #
    @16
    @17
    wph
    cX
    cc
    @14
    @0
    wph
    vx
    vy
    cX
    cX
    cX
    cmin
    cc
    cc
    cc
    cF
    cG
    cvv
    cvv
    @14
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @14
    @19
    cmin
    co
    cc
    wcel
    wph
    @14
    @19
    subcl
    adantl
    dv11cn.f
    dv11cn.g
    @11
    @11
    @12
    off
    #
    ffvelrnda
    #
    @16
    @17
    cabs
    cfv
    #
    cc0
    wceq
    #
    @22
    cc0
    cle
    wbr
    #
    cc0
    @22
    cle
    wbr
    #
    @16
    @17
    cC
    @0
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cc0
    @14
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @22
    cc0
    cle
    wph
    @15
    @15
    cC
    cX
    wcel
    #
    wa
    @28
    @31
    cle
    wbr
    @16
    @15
    @32
    wph
    @15
    simpr
    wph
    @32
    @15
    dv11cn.c
    adantr
    jca
    wph
    vx
    cA
    cX
    cR
    @0
    cc0
    cX
    @14
    cC
    wph
    cX
    @10
    cc
    dv11cn.x
    wph
    @8
    cc
    cxmt
    cfv
    wcel
    #
    cA
    cc
    wcel
    cR
    cxr
    wcel
    @10
    cc
    wss
    @33
    wph
    cnxmet
    a1i
    dv11cn.a
    dv11cn.r
    @8
    cA
    cR
    cc
    blssm
    syl3anc
    syl5eqss
    #
    @20
    dv11cn.a
    dv11cn.r
    dv11cn.x
    wph
    cc
    @0
    cdv
    co
    #
    cdm
    #
    cX
    wceq
    cX
    @36
    wss
    wph
    @36
    @2
    cdm
    #
    cX
    wph
    @35
    @2
    wph
    @35
    cc
    vx
    cX
    @14
    cF
    cfv
    #
    @14
    cG
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    @14
    cc
    cF
    cdv
    co
    #
    cfv
    #
    @43
    cmin
    co
    #
    cmpt
    #
    @2
    wph
    @0
    @41
    cc
    cdv
    wph
    vx
    cX
    @38
    @39
    cmin
    cF
    cG
    cvv
    cc
    cc
    @11
    wph
    cX
    cc
    @14
    cF
    dv11cn.f
    ffvelrnda
    #
    wph
    cX
    cc
    @14
    cG
    dv11cn.g
    ffvelrnda
    #
    wph
    vx
    cX
    cc
    cF
    dv11cn.f
    feqmptd
    #
    wph
    vx
    cX
    cc
    cG
    dv11cn.g
    feqmptd
    #
    offval2
    #
    oveq2d
    wph
    vx
    @38
    @43
    @39
    @43
    cc
    cvv
    cvv
    cX
    cc
    cr
    cc
    cpr
    wcel
    wph
    cnelprrecn
    a1i
    @46
    @16
    @14
    @42
    fvexd
    #
    wph
    @42
    cc
    vx
    cX
    @38
    cmpt
    #
    cdv
    co
    vx
    cX
    @43
    cmpt
    #
    wph
    cF
    @52
    cc
    cdv
    @48
    oveq2d
    wph
    vx
    cX
    cc
    @42
    wph
    @42
    cdm
    #
    cc
    @42
    wf
    cX
    cc
    @42
    wf
    cF
    dvfcn
    wph
    @54
    cX
    cc
    @42
    dv11cn.d
    feq2d
    mpbii
    #
    feqmptd
    #
    eqtr3d
    @47
    @51
    wph
    @42
    cc
    cG
    cdv
    co
    @53
    cc
    vx
    cX
    @39
    cmpt
    #
    cdv
    co
    dv11cn.e
    @56
    wph
    cG
    @57
    cc
    cdv
    @49
    oveq2d
    3eqtr3rd
    dvmptsub
    wph
    @45
    vx
    cX
    cc0
    cmpt
    @2
    wph
    vx
    cX
    @44
    cc0
    @16
    @43
    wph
    cX
    cc
    @14
    @42
    @55
    ffvelrnda
    subidd
    mpteq2dva
    vx
    cX
    cc0
    fconstmpt
    syl6eqr
    3eqtrd
    #
    dmeqd
    @13
    @1
    c0
    wne
    @37
    cX
    wceq
    0cn
    cc0
    cc
    snnzg
    cX
    @1
    dmxp
    mp2b
    syl6eq
    cX
    @36
    eqimss2
    syl
    wph
    0red
    @16
    @14
    @35
    cfv
    #
    cabs
    cfv
    cc0
    cc0
    cle
    @16
    @59
    wph
    @15
    @59
    @18
    cc0
    wph
    @14
    @35
    @2
    @58
    fveq1d
    cX
    cc0
    @14
    c0ex
    fvconst2
    #
    sylan9eq
    abs00bd
    0le0
    syl6eqbr
    dvlipcn
    syldan
    @16
    @27
    @17
    cabs
    @16
    @27
    @17
    cc0
    cmin
    co
    @17
    @16
    @26
    cc0
    @17
    cmin
    wph
    @26
    cc0
    wceq
    @15
    wph
    @26
    cC
    @41
    cfv
    #
    cC
    cF
    cfv
    #
    cC
    cG
    cfv
    #
    cmin
    co
    #
    cc0
    wph
    cC
    @0
    @41
    @50
    fveq1d
    wph
    @32
    @61
    @64
    wceq
    dv11cn.c
    vx
    cC
    @40
    @64
    cX
    @41
    @14
    cC
    wceq
    @38
    @62
    @39
    @63
    cmin
    @14
    cC
    cF
    fveq2
    @14
    cC
    cG
    fveq2
    oveq12d
    @41
    eqid
    @62
    @63
    cmin
    ovex
    fvmpt
    syl
    wph
    @62
    @63
    wph
    cX
    cc
    cC
    cF
    dv11cn.f
    dv11cn.c
    ffvelrnd
    dv11cn.p
    subeq0bd
    3eqtrd
    adantr
    oveq2d
    @16
    @17
    @21
    subid1d
    eqtrd
    fveq2d
    @16
    @30
    @16
    @30
    @16
    @29
    @16
    @14
    cC
    wph
    cX
    cc
    @14
    @34
    sselda
    wph
    cC
    cc
    wcel
    @15
    wph
    cX
    cc
    cC
    @34
    dv11cn.c
    sseldd
    adantr
    subcld
    abscld
    recnd
    mul02d
    3brtr3d
    @16
    @17
    @21
    absge0d
    @16
    @22
    cr
    wcel
    cc0
    cr
    wcel
    @23
    @24
    @25
    wa
    wb
    @16
    @17
    @21
    abscld
    0re
    @22
    cc0
    letri3
    sylancl
    mpbir2and
    abs00d
    @15
    @18
    cc0
    wceq
    wph
    @60
    adantl
    eqtr4d
    eqfnfvd
    wph
    @7
    @5
    @6
    @3
    @4
    wb
    @11
    dv11cn.f
    dv11cn.g
    cX
    cF
    cG
    cvv
    ofsubeq0
    syl3anc
    mpbid
end
