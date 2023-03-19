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
include "simp2.mm"
include "3adant3.mm"
include "mat1comp.mm"
include "syl2anc.mm"
include "ifnefalse.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "suppsssn.mm"
include "gsumpt.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antll.mm"
include "equequ1.mm"
include "ifbid.mm"
include "equequ2.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "cur.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ovmpt2.mm"
include "anidms.mm"
include "fovrnda.mm"
include "ringridm.mm"
include "3eqtrd.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "wb.mm"
include "mamucl.mm"
include "ffn.mm"
include "eqfnov2.mm"
include "mpbird.mm"

theorem mamurid
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
  let cA: class A
  let cJ: class J
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  assume mamumat1cl.b: |- B = ( Base ` R )
  assume mamumat1cl.r: |- ( ph -> R e. Ring )
  assume mamumat1cl.o: |- .1. = ( 1r ` R )
  assume mamumat1cl.z: |- .0. = ( 0g ` R )
  assume mamumat1cl.i: |- I = ( i e. M , j e. M |-> if ( i = j , .1. , .0. ) )
  assume mamumat1cl.m: |- ( ph -> M e. Fin )
  assume mamulid.n: |- ( ph -> N e. Fin )
  assume mamurid.f: |- F = ( R maMul <. N , M , M >. )
  assume mamurid.x: |- ( ph -> X e. ( B ^m ( N X. M ) ) )

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
  disjoint B k
  disjoint .0. k
  disjoint F l
  disjoint F m
  disjoint R k
  assert |- ( ph -> ( X F I ) = X )

  proof
    wph
    cX
    cI
    cF
    co
    #
    cX
    wceq
    #
    vl
    cv
    #
    vm
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
    vm
    cM
    wral
    vl
    cN
    wral
    #
    wph
    @6
    vl
    vm
    cN
    cM
    wph
    @2
    cN
    wcel
    #
    @3
    cM
    wcel
    #
    wa
    #
    wa
    #
    @4
    cR
    vk
    cM
    @2
    vk
    cv
    #
    cX
    co
    #
    @12
    @3
    cI
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
    @3
    @17
    cfv
    #
    @5
    @11
    cB
    cM
    cR
    @15
    vk
    cF
    @2
    @3
    cN
    cM
    crg
    cX
    cI
    mamurid.f
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
    cN
    cfn
    wcel
    @10
    mamulid.n
    adantr
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
    cX
    cB
    cN
    cM
    cxp
    #
    cmap
    co
    #
    wcel
    #
    @10
    mamurid.x
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
    @8
    @9
    simprl
    wph
    @8
    @9
    simprr
    #
    mamufv
    @11
    cM
    cB
    @17
    cR
    cfn
    @3
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
    vk
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
    #
    @14
    cB
    wcel
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
    cN
    cM
    cX
    wph
    @23
    cB
    cX
    wf
    #
    @10
    @30
    wph
    @25
    @34
    mamurid.x
    cX
    cB
    @23
    elmapi
    syl
    #
    ad2antrr
    wph
    @8
    @9
    @30
    simplrl
    @11
    @30
    simpr
    #
    fovrnd
    #
    @31
    @12
    @3
    cB
    cM
    cM
    cI
    wph
    @26
    cB
    cI
    wf
    #
    @10
    @30
    wph
    @27
    @38
    @28
    cI
    cB
    @26
    elmapi
    syl
    ad2antrr
    @36
    wph
    @8
    @9
    @30
    simplrr
    #
    fovrnd
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
    vk
    cfn
    @3
    c.0
    @11
    @30
    @12
    @3
    wne
    #
    w3a
    #
    @16
    @13
    c.0
    @15
    co
    #
    c.0
    @42
    @14
    c.0
    @13
    @15
    @42
    @14
    vk
    vm
    weq
    #
    c.1
    c.0
    cif
    #
    c.0
    @42
    @30
    @9
    @14
    @45
    wceq
    @11
    @30
    @41
    simp2
    @11
    @30
    @9
    @41
    @39
    3adant3
    wph
    @12
    cB
    cR
    c.1
    vi
    vj
    cI
    @3
    cM
    c.0
    mamumat1cl.b
    mamumat1cl.r
    mamumat1cl.o
    mamumat1cl.z
    mamumat1cl.i
    mamumat1cl.m
    mat1comp
    syl2anc
    @41
    @11
    @45
    c.0
    wceq
    @30
    @12
    @3
    c.1
    c.0
    ifnefalse
    3ad2ant3
    eqtrd
    oveq2d
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
    @46
    @33
    @37
    cB
    cR
    @15
    @13
    c.0
    mamumat1cl.b
    @19
    mamumat1cl.z
    ringrz
    syl2anc
    3adant3
    eqtrd
    @22
    suppsssn
    gsumpt
    @11
    @18
    @5
    @3
    @3
    cI
    co
    #
    @15
    co
    #
    @5
    c.1
    @15
    co
    #
    @5
    @9
    @18
    @48
    wceq
    wph
    @8
    vk
    @3
    @16
    @48
    cM
    @17
    @44
    @13
    @5
    @14
    @47
    @15
    @12
    @3
    @2
    cX
    oveq2
    @12
    @3
    @3
    cI
    oveq1
    oveq12d
    @40
    @5
    @47
    @15
    ovex
    fvmpt
    ad2antll
    @9
    @48
    @49
    wceq
    wph
    @8
    @9
    @47
    c.1
    @5
    @15
    @9
    @47
    c.1
    wceq
    vi
    vj
    @3
    @3
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
    vm
    vj
    weq
    #
    c.1
    c.0
    cif
    #
    vi
    vm
    weq
    @50
    @51
    c.1
    c.0
    vi
    vm
    vj
    equequ1
    ifbid
    vj
    vm
    weq
    #
    @52
    vm
    vm
    weq
    #
    c.1
    c.0
    cif
    c.1
    @53
    @51
    @54
    c.1
    c.0
    vj
    vm
    vm
    equequ2
    ifbid
    @54
    c.1
    c.0
    @3
    eqid
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
    oveq2d
    ad2antll
    @11
    @20
    @5
    cB
    wcel
    @49
    @5
    wceq
    @21
    wph
    @2
    @3
    cB
    cN
    cM
    cX
    @35
    fovrnda
    cB
    cR
    @15
    c.1
    @5
    mamumat1cl.b
    @19
    mamumat1cl.o
    ringridm
    syl2anc
    3eqtrd
    3eqtrd
    ralrimivva
    wph
    @0
    @23
    wfn
    #
    cX
    @23
    wfn
    #
    @1
    @7
    wb
    wph
    @23
    cB
    @0
    wf
    #
    @55
    wph
    @0
    @24
    wcel
    @57
    wph
    cB
    cM
    cR
    cF
    cN
    cM
    cX
    cI
    mamumat1cl.b
    mamumat1cl.r
    mamurid.f
    mamulid.n
    mamumat1cl.m
    mamumat1cl.m
    mamurid.x
    @28
    mamucl
    @0
    cB
    @23
    elmapi
    syl
    @23
    cB
    @0
    ffn
    syl
    wph
    @34
    @56
    @35
    @23
    cB
    cX
    ffn
    syl
    vl
    vm
    cN
    cM
    @0
    cX
    eqfnov2
    syl2anc
    mpbird
end
