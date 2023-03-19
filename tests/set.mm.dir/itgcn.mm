include "cv.mm"
include "cvol.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wss.mm"
include "wa.mm"
include "citg.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "abscld.mm"
include "absge0d.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0icopnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "rembl.mm"
include "cdif.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "iblabs.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simpld.mm"
include "syl5eqel.mm"
include "mbfss.mm"
include "simprd.mm"
include "itg2cn.mm"
include "cc.mm"
include "simprr.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "simprl.mm"
include "iblss.mm"
include "itgposval.mm"
include "sseld.mm"
include "pm4.71d.mm"
include "ifbid.mm"
include "ifan.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfif.mm"
include "wceq.mm"
include "elequ1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "cvv.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "ifeq1d.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "breq1d.mm"
include "biimprd.mm"
include "imim2d.mm"
include "expr.mm"
include "com23.mm"
include "imp4a.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"

theorem itgcn
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vd: setvar d
  let vy: setvar y
  assume itgcn.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgcn.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgcn.3: |- ( ph -> C e. RR+ )

  disjoint d u
  disjoint d x
  disjoint A d
  disjoint u x
  disjoint A u
  disjoint A x
  disjoint B d
  disjoint B u
  disjoint C d
  disjoint C u
  disjoint d ph
  disjoint ph u
  disjoint ph x
  disjoint d y
  disjoint u y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint ph y
  assert |- ( ph -> E. d e. RR+ A. u e. dom vol ( ( u C_ A /\ ( vol ` u ) < d ) -> S. u ( abs ` B ) _d x < C ) )

  proof
    wph
    vu
    cv
    #
    cvol
    cfv
    vd
    cv
    clt
    wbr
    #
    vy
    cr
    vy
    cv
    #
    @0
    wcel
    #
    @2
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cC
    clt
    wbr
    #
    wi
    #
    vu
    cvol
    cdm
    #
    wral
    #
    vd
    crp
    wrex
    @0
    cA
    wss
    #
    @1
    wa
    vx
    @0
    @6
    citg
    #
    cC
    clt
    wbr
    #
    wi
    #
    vu
    @15
    wral
    #
    vd
    crp
    wrex
    wph
    vy
    vu
    cC
    @8
    vd
    wph
    vx
    cr
    @7
    cc0
    cpnf
    cico
    co
    #
    @8
    wph
    @7
    @22
    wcel
    #
    @4
    cr
    wcel
    #
    wph
    @5
    @6
    cc0
    @22
    wph
    @5
    wa
    #
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    @6
    @22
    wcel
    @25
    cB
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @26
    cmbf
    wcel
    itgcn.2
    @26
    iblmbf
    syl
    #
    itgcn.1
    mbfmptcl
    #
    abscld
    #
    @25
    cB
    @28
    absge0d
    #
    @6
    elrege0
    sylanbrc
    cc0
    @22
    wcel
    wph
    @5
    wn
    #
    wa
    0e0icopnf
    a1i
    ifclda
    #
    adantr
    @8
    eqid
    #
    fmptd
    wph
    vx
    cA
    cr
    @7
    @22
    wph
    cA
    @15
    wcel
    cA
    cr
    wss
    wph
    vx
    cA
    cB
    cV
    @27
    itgcn.1
    mbfdm2
    cA
    mblss
    syl
    cr
    @15
    wcel
    wph
    rembl
    a1i
    wph
    @23
    @5
    @32
    adantr
    wph
    @4
    cr
    cA
    cdif
    wcel
    #
    wa
    @5
    @6
    cc0
    @34
    @31
    wph
    @4
    cr
    cA
    eldifn
    adantl
    iffalsed
    wph
    vx
    cA
    @7
    cmpt
    vx
    cA
    @6
    cmpt
    #
    cmbf
    vx
    cA
    @7
    @6
    @5
    @6
    cc0
    iftrue
    mpteq2ia
    wph
    @35
    cmbf
    wcel
    #
    @8
    citg2
    cfv
    cr
    wcel
    #
    wph
    @35
    cibl
    wcel
    #
    @36
    @37
    wa
    wph
    vx
    cA
    cB
    cV
    itgcn.1
    itgcn.2
    iblabs
    #
    wph
    vx
    cA
    @6
    @29
    @30
    iblpos
    mpbid
    #
    simpld
    syl5eqel
    mbfss
    wph
    @36
    @37
    @40
    simprd
    itgcn.3
    itg2cn
    wph
    @16
    @21
    vd
    crp
    wph
    @14
    @20
    vu
    @15
    wph
    @0
    @15
    wcel
    #
    wa
    #
    @14
    @17
    @1
    @19
    @42
    @17
    @14
    @1
    @19
    wi
    #
    wph
    @41
    @17
    @14
    @43
    wi
    wph
    @41
    @17
    wa
    #
    wa
    #
    @13
    @19
    @1
    @45
    @19
    @13
    @45
    @18
    @12
    cC
    clt
    @45
    @18
    vx
    cr
    @4
    @0
    wcel
    #
    @7
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @12
    @45
    @18
    vx
    cr
    @46
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @49
    @45
    vx
    @0
    @6
    @45
    @46
    wa
    #
    cB
    @45
    @46
    @5
    cB
    cc
    wcel
    #
    @45
    @0
    cA
    @4
    wph
    @41
    @17
    simprr
    #
    sselda
    wph
    @5
    @53
    @44
    @28
    adantlr
    #
    syldan
    #
    abscld
    @45
    vx
    @0
    cA
    @6
    cr
    @54
    wph
    @41
    @17
    simprl
    @45
    @5
    wa
    cB
    @55
    abscld
    wph
    @38
    @44
    @39
    adantr
    iblss
    @52
    cB
    @56
    absge0d
    itgposval
    @45
    @51
    @48
    citg2
    @45
    vx
    cr
    @50
    @47
    @45
    @50
    @46
    @5
    wa
    #
    @6
    cc0
    cif
    @47
    @45
    @46
    @57
    @6
    cc0
    @45
    @46
    @5
    @45
    @0
    cA
    @4
    @54
    sseld
    pm4.71d
    ifbid
    @46
    @5
    @6
    cc0
    ifan
    syl6eq
    mpteq2dv
    fveq2d
    eqtrd
    @11
    @48
    citg2
    @11
    vx
    cr
    @46
    @4
    @8
    cfv
    #
    cc0
    cif
    #
    cmpt
    @48
    vy
    vx
    cr
    @10
    @59
    @3
    vx
    @9
    cc0
    @3
    vx
    nfv
    vx
    cr
    @7
    @2
    nffvmpt1
    vx
    cc0
    nfcv
    nfif
    vy
    @59
    nfcv
    @2
    @4
    wceq
    @3
    @46
    @9
    @58
    cc0
    vy
    vx
    vu
    elequ1
    @2
    @4
    @8
    fveq2
    ifbieq1d
    cbvmpt
    vx
    cr
    @59
    @47
    @24
    @46
    @58
    @7
    cc0
    @24
    @7
    cvv
    wcel
    @58
    @7
    wceq
    @5
    @6
    cc0
    cB
    cabs
    fvex
    c0ex
    ifex
    vx
    cr
    @7
    cvv
    @8
    @33
    fvmpt2
    mpan2
    ifeq1d
    mpteq2ia
    eqtri
    fveq2i
    syl6eqr
    breq1d
    biimprd
    imim2d
    expr
    com23
    imp4a
    ralimdva
    reximdv
    mpd
end
