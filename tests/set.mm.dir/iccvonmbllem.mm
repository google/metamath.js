include "cv.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cixp.mm"
include "cn.mm"
include "cioo.mm"
include "ciin.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "cmpt.mm"
include "cvv.mm"
include "a1i.mm"
include "cfn.mm"
include "adantr.mm"
include "mptexd.mm"
include "fvmpt2d.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "nnrecre.mm"
include "ad2antlr.mm"
include "resubcld.mm"
include "an32s.mm"
include "readdcld.mm"
include "oveq12d.mm"
include "iineq2dv.mm"
include "iooiinicc.mm"
include "eqtrd.mm"
include "ixpeq2dva.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "c0.mm"
include "wne.mm"
include "nnn0.mm"
include "ixpiin.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "dmovnsal.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "nnct.mm"
include "cxr.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "wss.mm"
include "ressxr.mm"
include "fssd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "ioovonmbl.mm"
include "saliincl.mm"
include "eqeltrd.mm"

theorem iccvonmbllem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume iccvonmbllem.x: |- ( ph -> X e. Fin )
  assume iccvonmbllem.s: |- S = dom ( voln ` X )
  assume iccvonmbllem.a: |- ( ph -> A : X --> RR )
  assume iccvonmbllem.b: |- ( ph -> B : X --> RR )
  assume iccvonmbllem.c: |- C = ( n e. NN |-> ( i e. X |-> ( ( A ` i ) - ( 1 / n ) ) ) )
  assume iccvonmbllem.d: |- D = ( n e. NN |-> ( i e. X |-> ( ( B ` i ) + ( 1 / n ) ) ) )

  disjoint A n
  disjoint B n
  disjoint C i
  disjoint D i
  disjoint S n
  disjoint X i
  disjoint X n
  disjoint i n
  disjoint i ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) [,] ( B ` i ) ) e. S )

  proof
    wph
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @0
    cB
    cfv
    #
    cicc
    co
    #
    cixp
    #
    vn
    cn
    vi
    cX
    @0
    vn
    cv
    #
    cC
    cfv
    #
    cfv
    #
    @0
    @5
    cD
    cfv
    #
    cfv
    #
    cioo
    co
    #
    cixp
    #
    ciin
    #
    cS
    wph
    @4
    vi
    cX
    vn
    cn
    @10
    ciin
    #
    cixp
    #
    @4
    @12
    wph
    @14
    @4
    wph
    vi
    cX
    @13
    @3
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @13
    vn
    cn
    @1
    c1
    @5
    cdiv
    co
    #
    cmin
    co
    #
    @2
    @17
    caddc
    co
    #
    cioo
    co
    #
    ciin
    @3
    @16
    vn
    cn
    @10
    @20
    @16
    @5
    cn
    wcel
    #
    wa
    @7
    @18
    @9
    @19
    cioo
    wph
    @21
    @15
    @7
    @18
    wceq
    wph
    @21
    wa
    #
    vi
    cX
    @18
    @6
    cr
    wph
    vn
    cn
    vi
    cX
    @18
    cmpt
    #
    cC
    cvv
    cC
    vn
    cn
    @23
    cmpt
    wceq
    wph
    iccvonmbllem.c
    a1i
    @22
    vi
    cX
    @18
    cfn
    wph
    cX
    cfn
    wcel
    @21
    iccvonmbllem.x
    adantr
    #
    mptexd
    fvmpt2d
    #
    @22
    @15
    wa
    #
    @1
    @17
    wph
    @15
    @1
    cr
    wcel
    @21
    wph
    cX
    cr
    @0
    cA
    iccvonmbllem.a
    ffvelrnda
    #
    adantlr
    @21
    @17
    cr
    wcel
    wph
    @15
    @5
    nnrecre
    ad2antlr
    #
    resubcld
    #
    fvmpt2d
    an32s
    wph
    @21
    @15
    @9
    @19
    wceq
    @22
    vi
    cX
    @19
    @8
    cr
    wph
    vn
    cn
    vi
    cX
    @19
    cmpt
    #
    cD
    cvv
    cD
    vn
    cn
    @30
    cmpt
    wceq
    wph
    iccvonmbllem.d
    a1i
    @22
    vi
    cX
    @19
    cfn
    @24
    mptexd
    fvmpt2d
    #
    @26
    @2
    @17
    wph
    @15
    @2
    cr
    wcel
    @21
    wph
    cX
    cr
    @0
    cB
    iccvonmbllem.b
    ffvelrnda
    #
    adantlr
    @28
    readdcld
    #
    fvmpt2d
    an32s
    oveq12d
    iineq2dv
    @16
    @1
    @2
    vn
    @27
    @32
    iooiinicc
    eqtrd
    ixpeq2dva
    eqcomd
    wph
    @4
    eqidd
    wph
    cn
    c0
    wne
    #
    @14
    @12
    wceq
    @34
    wph
    nnn0
    a1i
    #
    vi
    vn
    cX
    cn
    @10
    ixpiin
    syl
    3eqtr3d
    wph
    cS
    vn
    @11
    cn
    wph
    cS
    cX
    iccvonmbllem.x
    iccvonmbllem.s
    dmovnsal
    cn
    com
    cdom
    wbr
    wph
    nnct
    a1i
    @35
    @22
    @6
    @8
    cS
    vi
    cX
    @24
    iccvonmbllem.s
    @22
    cX
    cxr
    @6
    wf
    cX
    cxr
    @23
    wf
    @22
    cX
    cr
    cxr
    @23
    @22
    vi
    cX
    @18
    cr
    @23
    @29
    @23
    eqid
    fmptd
    cr
    cxr
    wss
    @22
    ressxr
    a1i
    #
    fssd
    @22
    cX
    cxr
    @6
    @23
    @25
    feq1d
    mpbird
    @22
    cX
    cxr
    @8
    wf
    cX
    cxr
    @30
    wf
    @22
    cX
    cr
    cxr
    @30
    @22
    vi
    cX
    @19
    cr
    @30
    @33
    @30
    eqid
    fmptd
    @36
    fssd
    @22
    cX
    cxr
    @8
    @30
    @31
    feq1d
    mpbird
    ioovonmbl
    saliincl
    eqeltrd
end
