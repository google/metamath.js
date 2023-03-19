include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "eqid.mm"
include "adantr.mm"
include "cfn.mm"
include "cxp.mm"
include "cmap.mm"
include "mamumat1cl.mm"
include "simprl.mm"
include "simprr.mm"
include "mamufv.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wf.mm"
include "elmapi.mm"
include "simplrl.mm"
include "simpr.mm"
include "fovrnd.mm"
include "simplrr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "wne.mm"
include "w3a.mm"
include "weq.mm"
include "cif.mm"
include "3adant3.mm"
include "simp2.mm"
include "mat1comp.mm"
include "wb.mm"
include "equcom.mm"
include "a1i.mm"
include "ifbid.mm"
include "eqtrd.mm"
include "syl2anc.mm"
include "ifnefalse.mm"
include "3ad2ant3.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "suppsssn.mm"
include "gsumpt.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "equequ1.mm"
include "equequ2.mm"
include "equid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "cur.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ovmpt2.mm"
include "anidms.mm"
include "fovrnda.mm"
include "ringlidm.mm"
include "3eqtrd.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "mamucl.mm"
include "ffn.mm"
include "eqfnov2.mm"
include "mpbird.mm"

theorem mamulid
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vm: setvar m
  let vk: setvar k
  let vl: setvar l
  let cA: class A
  let cJ: class J
  assume mamumat1cl.b: |- B = ( Base ` R )
  assume mamumat1cl.r: |- ( ph -> R e. Ring )
  assume mamumat1cl.o: |- .1. = ( 1r ` R )
  assume mamumat1cl.z: |- .0. = ( 0g ` R )
  assume mamumat1cl.i: |- I = ( i e. M , j e. M |-> if ( i = j , .1. , .0. ) )
  assume mamumat1cl.m: |- ( ph -> M e. Fin )
  assume mamulid.n: |- ( ph -> N e. Fin )
  assume mamulid.f: |- F = ( R maMul <. M , M , N >. )
  assume mamulid.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )

  disjoint i j
  disjoint B i
  disjoint B j
  disjoint M i
  disjoint M j
  disjoint i ph
  disjoint j ph
  disjoint .0. i
  disjoint .0. j
  disjoint .1. i
  disjoint .1. j
  disjoint B m
  disjoint .0. m
  disjoint k l
  disjoint F k
  disjoint F l
  disjoint R m
  disjoint A i
  disjoint A j
  disjoint J i
  disjoint J j
  disjoint k l
  disjoint k m
  disjoint k ph
  disjoint l m
  disjoint l ph
  disjoint m ph
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint M k
  disjoint M l
  disjoint M m
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint X k
  disjoint X l
  disjoint X m
  assert |- ( ph -> ( I F X ) = X )

  proof
    wph
    cI
    cX
    cF
    co
    #
    cX
    wceq
    #
    vl
    cv
    #
    vk
    cv
    #
    @0
    co
    #
    @2
    @3
    cX
    co
    #
    wceq
    #
    vk
    cN
    wral
    vl
    cM
    wral
    #
    wph
    @6
    vl
    vk
    cM
    cN
    wph
    @2
    cM
    wcel
    #
    @3
    cN
    wcel
    #
    wa
    #
    wa
    #
    @4
    cR
    vm
    cM
    @2
    vm
    cv
    #
    cI
    co
    #
    @12
    @3
    cX
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    @2
    @17
    cfv
    #
    @5
    @11
    cB
    cN
    cR
    @15
    vm
    cF
    @2
    @3
    cM
    cM
    crg
    cI
    cX
    mamulid.f
    mamumat1cl.b
    @15
    eqid
    #
    wph
    cR
    crg
    wcel
    #
    @10
    mamumat1cl.r
    adantr
    #
    wph
    cM
    cfn
    wcel
    @10
    mamumat1cl.m
    adantr
    #
    @22
    wph
    cN
    cfn
    wcel
    @10
    mamulid.n
    adantr
    wph
    cI
    cB
    cM
    cM
    cxp
    #
    cmap
    co
    wcel
    #
    @10
    wph
    cB
    cR
    c.1
    vi
    vj
    cI
    cM
    c.0
    mamumat1cl.b
    mamumat1cl.r
    mamumat1cl.o
    mamumat1cl.z
    mamumat1cl.i
    mamumat1cl.m
    mamumat1cl
    #
    adantr
    wph
    cX
    cB
    cM
    cN
    cxp
    #
    cmap
    co
    #
    wcel
    #
    @10
    mamulid.x
    adantr
    wph
    @8
    @9
    simprl
    #
    wph
    @8
    @9
    simprr
    mamufv
    @11
    cM
    cB
    @17
    cR
    cfn
    @2
    c.0
    mamumat1cl.b
    mamumat1cl.z
    @11
    @20
    cR
    cmnd
    wcel
    @21
    cR
    ringmnd
    syl
    @22
    @29
    @11
    vm
    cM
    @16
    cB
    @17
    @11
    @12
    cM
    wcel
    #
    wa
    #
    @20
    @13
    cB
    wcel
    @14
    cB
    wcel
    #
    @16
    cB
    wcel
    wph
    @20
    @10
    @30
    mamumat1cl.r
    ad2antrr
    #
    @31
    @2
    @12
    cB
    cM
    cM
    cI
    wph
    @23
    cB
    cI
    wf
    #
    @10
    @30
    wph
    @24
    @34
    @25
    cI
    cB
    @23
    elmapi
    syl
    ad2antrr
    wph
    @8
    @9
    @30
    simplrl
    #
    @11
    @30
    simpr
    #
    fovrnd
    @31
    @12
    @3
    cB
    cM
    cN
    cX
    wph
    @26
    cB
    cX
    wf
    #
    @10
    @30
    wph
    @28
    @37
    mamulid.x
    cX
    cB
    @26
    elmapi
    syl
    #
    ad2antrr
    @36
    wph
    @8
    @9
    @30
    simplrr
    fovrnd
    #
    cB
    cR
    @15
    @13
    @14
    mamumat1cl.b
    @19
    ringcl
    syl3anc
    @17
    eqid
    #
    fmptd
    @11
    cM
    @16
    vm
    cfn
    @2
    c.0
    @11
    @30
    @12
    @2
    wne
    #
    w3a
    #
    @16
    c.0
    @14
    @15
    co
    #
    c.0
    @42
    @13
    c.0
    @14
    @15
    @42
    @13
    vm
    vl
    weq
    #
    c.1
    c.0
    cif
    #
    c.0
    @42
    @8
    @30
    @13
    @45
    wceq
    @11
    @30
    @8
    @41
    @35
    3adant3
    @11
    @30
    @41
    simp2
    @8
    @30
    wa
    #
    @13
    vl
    vm
    weq
    #
    c.1
    c.0
    cif
    @45
    wph
    @2
    cB
    cR
    c.1
    vi
    vj
    cI
    @12
    cM
    c.0
    mamumat1cl.b
    mamumat1cl.r
    mamumat1cl.o
    mamumat1cl.z
    mamumat1cl.i
    mamumat1cl.m
    mat1comp
    @46
    @47
    @44
    c.1
    c.0
    @47
    @44
    wb
    @46
    vl
    vm
    equcom
    a1i
    ifbid
    eqtrd
    syl2anc
    @41
    @11
    @45
    c.0
    wceq
    @30
    @12
    @2
    c.1
    c.0
    ifnefalse
    3ad2ant3
    eqtrd
    oveq1d
    @11
    @30
    @43
    c.0
    wceq
    #
    @41
    @31
    @20
    @32
    @48
    @33
    @39
    cB
    cR
    @15
    @14
    c.0
    mamumat1cl.b
    @19
    mamumat1cl.z
    ringlz
    syl2anc
    3adant3
    eqtrd
    @22
    suppsssn
    gsumpt
    @11
    @18
    @2
    @2
    cI
    co
    #
    @5
    @15
    co
    #
    c.1
    @5
    @15
    co
    #
    @5
    @8
    @18
    @50
    wceq
    wph
    @9
    vm
    @2
    @16
    @50
    cM
    @17
    @44
    @13
    @49
    @14
    @5
    @15
    @12
    @2
    @2
    cI
    oveq2
    @12
    @2
    @3
    cX
    oveq1
    oveq12d
    @40
    @49
    @5
    @15
    ovex
    fvmpt
    ad2antrl
    @11
    @49
    c.1
    @5
    @15
    @8
    @49
    c.1
    wceq
    #
    wph
    @9
    @8
    @52
    vi
    vj
    @2
    @2
    cM
    cM
    vi
    vj
    weq
    #
    c.1
    c.0
    cif
    c.1
    cI
    vl
    vj
    weq
    #
    c.1
    c.0
    cif
    #
    vi
    vl
    weq
    @53
    @54
    c.1
    c.0
    vi
    vl
    vj
    equequ1
    ifbid
    vj
    vl
    weq
    #
    @55
    vl
    vl
    weq
    #
    c.1
    c.0
    cif
    c.1
    @56
    @54
    @57
    c.1
    c.0
    vj
    vl
    vl
    equequ2
    ifbid
    @57
    c.1
    c.0
    vl
    equid
    iftruei
    syl6eq
    mamumat1cl.i
    c.1
    cR
    cur
    cfv
    cvv
    mamumat1cl.o
    cR
    cur
    fvex
    eqeltri
    ovmpt2
    anidms
    ad2antrl
    oveq1d
    @11
    @20
    @5
    cB
    wcel
    @51
    @5
    wceq
    @21
    wph
    @2
    @3
    cB
    cM
    cN
    cX
    @38
    fovrnda
    cB
    cR
    @15
    c.1
    @5
    mamumat1cl.b
    @19
    mamumat1cl.o
    ringlidm
    syl2anc
    3eqtrd
    3eqtrd
    ralrimivva
    wph
    @0
    @26
    wfn
    #
    cX
    @26
    wfn
    #
    @1
    @7
    wb
    wph
    @26
    cB
    @0
    wf
    #
    @58
    wph
    @0
    @27
    wcel
    @60
    wph
    cB
    cN
    cR
    cF
    cM
    cM
    cI
    cX
    mamumat1cl.b
    mamumat1cl.r
    mamulid.f
    mamumat1cl.m
    mamumat1cl.m
    mamulid.n
    @25
    mamulid.x
    mamucl
    @0
    cB
    @26
    elmapi
    syl
    @26
    cB
    @0
    ffn
    syl
    wph
    @37
    @59
    @38
    @26
    cB
    cX
    ffn
    syl
    vl
    vk
    cM
    cN
    @0
    cX
    eqfnov2
    syl2anc
    mpbird
end
