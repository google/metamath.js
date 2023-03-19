include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "cprod.mm"
include "cmpt.mm"
include "cli.mm"
include "cvoln.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "cixp.mm"
include "cvol.mm"
include "simpr.mm"
include "cvv.mm"
include "cdm.mm"
include "cfn.mm"
include "adantr.mm"
include "eqid.mm"
include "cr.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "nnrecre.mm"
include "ad2antlr.mm"
include "readdcld.mm"
include "fmptd.mm"
include "mptexd.mm"
include "fvmpt2d.mm"
include "feq1d.mm"
include "mpbird.mm"
include "hoimbl.mm"
include "elexd.mm"
include "syldan.mm"
include "fveq2d.mm"
include "c0.mm"
include "wne.mm"
include "vonn0hoi.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "syldanl.mm"
include "volico.mm"
include "syl2anc.mm"
include "cle.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "ltaddrpd.mm"
include "breqtrrd.mm"
include "lelttrd.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "prodeq2dv.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "recnd.mm"
include "addsubd.mm"
include "mpteq2dva.mm"
include "nfv.mm"
include "resubcld.mm"
include "fprodaddrecnncnv.mm"
include "eqbrtrd.mm"

theorem vonicclem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cX: class X
  let vx: setvar x
  assume vonicclem1.x: |- ( ph -> X e. Fin )
  assume vonicclem1.a: |- ( ph -> A : X --> RR )
  assume vonicclem1.b: |- ( ph -> B : X --> RR )
  assume vonicclem1.u: |- ( ph -> X =/= (/) )
  assume vonicclem1.t: |- ( ( ph /\ k e. X ) -> ( A ` k ) <_ ( B ` k ) )
  assume vonicclem1.c: |- C = ( n e. NN |-> ( k e. X |-> ( ( B ` k ) + ( 1 / n ) ) ) )
  assume vonicclem1.d: |- D = ( n e. NN |-> X_ k e. X ( ( A ` k ) [,) ( ( C ` n ) ` k ) ) )
  assume vonicclem1.s: |- S = ( n e. NN |-> ( ( voln ` X ) ` ( D ` n ) ) )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint B n
  disjoint C k
  disjoint X k
  disjoint X n
  disjoint k ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> S ~~> prod_ k e. X ( ( B ` k ) - ( A ` k ) ) )

  proof
    wph
    cS
    vn
    cn
    cX
    vk
    cv
    #
    cB
    cfv
    #
    @0
    cA
    cfv
    #
    cmin
    co
    #
    c1
    vn
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    vk
    cprod
    #
    cmpt
    #
    cX
    @3
    vk
    cprod
    cli
    wph
    cS
    vn
    cn
    @4
    cD
    cfv
    #
    cX
    cvoln
    cfv
    #
    cfv
    #
    cmpt
    #
    @8
    cS
    @12
    wceq
    wph
    vonicclem1.s
    a1i
    wph
    vn
    cn
    @11
    @7
    wph
    @4
    cn
    wcel
    #
    wa
    #
    @11
    cX
    @0
    @4
    cC
    cfv
    #
    cfv
    #
    @2
    cmin
    co
    #
    vk
    cprod
    #
    @7
    @14
    @11
    vk
    cX
    @2
    @16
    cico
    co
    #
    cixp
    #
    @10
    cfv
    cX
    @19
    cvol
    cfv
    #
    vk
    cprod
    @18
    @14
    @9
    @20
    @10
    wph
    @13
    @13
    @9
    @20
    wceq
    wph
    @13
    simpr
    #
    wph
    vn
    cn
    @20
    cD
    cvv
    cD
    vn
    cn
    @20
    cmpt
    wceq
    wph
    vonicclem1.d
    a1i
    @14
    @20
    @10
    cdm
    #
    @14
    cA
    @15
    @23
    vk
    cX
    wph
    cX
    cfn
    wcel
    @13
    vonicclem1.x
    adantr
    #
    @23
    eqid
    wph
    cX
    cr
    cA
    wf
    @13
    vonicclem1.a
    adantr
    #
    @14
    cX
    cr
    @15
    wf
    #
    cX
    cr
    vk
    cX
    @1
    @5
    caddc
    co
    #
    cmpt
    #
    wf
    @14
    vk
    cX
    @27
    cr
    @28
    @14
    @0
    cX
    wcel
    #
    wa
    #
    @1
    @5
    wph
    @29
    @1
    cr
    wcel
    #
    @13
    wph
    cX
    cr
    @0
    cB
    vonicclem1.b
    ffvelrnda
    #
    adantlr
    #
    @13
    @5
    cr
    wcel
    wph
    @29
    @4
    nnrecre
    ad2antlr
    #
    readdcld
    #
    @28
    eqid
    fmptd
    @14
    cX
    cr
    @15
    @28
    wph
    vn
    cn
    @28
    cC
    cvv
    cC
    vn
    cn
    @28
    cmpt
    wceq
    wph
    vonicclem1.c
    a1i
    wph
    @28
    cvv
    wcel
    @13
    wph
    vk
    cX
    @27
    cfn
    vonicclem1.x
    mptexd
    adantr
    fvmpt2d
    #
    feq1d
    mpbird
    #
    hoimbl
    elexd
    fvmpt2d
    syldan
    fveq2d
    @14
    cA
    @15
    vk
    @20
    cX
    @24
    wph
    cX
    c0
    wne
    @13
    vonicclem1.u
    adantr
    @25
    wph
    @13
    @13
    @26
    @22
    @37
    syldan
    #
    @20
    eqid
    vonn0hoi
    @14
    cX
    @21
    @17
    vk
    @30
    @21
    @2
    @16
    clt
    wbr
    #
    @17
    cc0
    cif
    #
    @17
    @30
    @2
    cr
    wcel
    #
    @16
    cr
    wcel
    @21
    @40
    wceq
    wph
    @13
    @13
    @29
    @41
    @22
    @14
    cX
    cr
    @0
    cA
    @25
    ffvelrnda
    #
    syldanl
    #
    @14
    cX
    cr
    @0
    @15
    @38
    ffvelrnda
    #
    @2
    @16
    volico
    syl2anc
    @30
    @39
    @17
    cc0
    @30
    @2
    @1
    @16
    @43
    wph
    @13
    @13
    @29
    @31
    @22
    @33
    syldanl
    #
    @44
    wph
    @29
    @2
    @1
    cle
    wbr
    @13
    vonicclem1.t
    adantlr
    @30
    @1
    @27
    @16
    clt
    @30
    @1
    @5
    @45
    @13
    @5
    crp
    wcel
    wph
    @29
    @13
    @4
    @4
    nnrp
    rpreccld
    ad2antlr
    ltaddrpd
    wph
    @13
    @13
    @29
    @16
    @27
    wceq
    @22
    @14
    vk
    cX
    @27
    @15
    cvv
    @36
    @30
    @27
    cr
    @35
    elexd
    fvmpt2d
    #
    syldanl
    breqtrrd
    lelttrd
    iftrued
    eqtrd
    prodeq2dv
    3eqtrd
    @14
    cX
    @17
    @6
    vk
    @30
    @17
    @27
    @2
    cmin
    co
    @6
    @30
    @16
    @27
    @2
    cmin
    @46
    oveq1d
    @30
    @1
    @5
    @2
    @30
    @1
    @33
    recnd
    @30
    @5
    @34
    recnd
    @30
    @2
    @42
    recnd
    addsubd
    eqtrd
    prodeq2dv
    eqtrd
    mpteq2dva
    eqtrd
    wph
    @3
    @8
    vk
    vn
    cX
    wph
    vk
    nfv
    vonicclem1.x
    wph
    @29
    wa
    #
    @3
    @47
    @1
    @2
    @32
    wph
    cX
    cr
    @0
    cA
    vonicclem1.a
    ffvelrnda
    resubcld
    recnd
    @8
    eqid
    fprodaddrecnncnv
    eqbrtrd
end
