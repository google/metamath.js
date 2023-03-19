include "cr.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cfn.mm"
include "cmpt.mm"
include "a1i.mm"
include "oveq2.mm"
include "eqeq1.mm"
include "prodeq1.mm"
include "ifbieq2d.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "wcel.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "fvmptd.mm"
include "wa.mm"
include "fveq1.mm"
include "adantr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "prodeq2ad.mm"
include "ifeq2d.mm"
include "wf.mm"
include "wb.mm"
include "reex.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "c0ex.mm"
include "prodex.mm"
include "ifex.mm"
include "ovmpt2d.mm"

theorem hoidmvval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume hoidmvval.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvval.a: |- ( ph -> A : X --> RR )
  assume hoidmvval.b: |- ( ph -> B : X --> RR )
  assume hoidmvval.x: |- ( ph -> X e. Fin )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( A ( L ` X ) B ) = if ( X = (/) , 0 , prod_ k e. X ( vol ` ( ( A ` k ) [,) ( B ` k ) ) ) ) )

  proof
    wph
    va
    vb
    cA
    cB
    cr
    cX
    cmap
    co
    #
    @0
    cX
    c0
    wceq
    #
    cc0
    cX
    vk
    cv
    #
    va
    cv
    #
    cfv
    #
    @2
    vb
    cv
    #
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cif
    #
    @1
    cc0
    cX
    @2
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cif
    #
    cX
    cL
    cfv
    cvv
    wph
    vx
    cX
    va
    vb
    cr
    vx
    cv
    #
    cmap
    co
    #
    @18
    @17
    c0
    wceq
    #
    cc0
    @17
    @8
    vk
    cprod
    #
    cif
    #
    cmpt2
    #
    va
    vb
    @0
    @0
    @10
    cmpt2
    #
    cfn
    cL
    cvv
    cL
    vx
    cfn
    @22
    cmpt
    wceq
    wph
    hoidmvval.l
    a1i
    @17
    cX
    wceq
    #
    @22
    @23
    wceq
    wph
    @24
    va
    vb
    @18
    @18
    @21
    @0
    @0
    @10
    @17
    cX
    cr
    cmap
    oveq2
    #
    @25
    @24
    @19
    @1
    @20
    @9
    cc0
    @17
    cX
    c0
    eqeq1
    @17
    cX
    @8
    vk
    prodeq1
    ifbieq2d
    mpt2eq123dv
    adantl
    hoidmvval.x
    @23
    cvv
    wcel
    wph
    va
    vb
    @0
    @0
    @10
    cr
    cX
    cmap
    ovex
    #
    @26
    mpt2ex
    a1i
    fvmptd
    @3
    cA
    wceq
    #
    @5
    cB
    wceq
    #
    wa
    #
    @10
    @16
    wceq
    wph
    @29
    @1
    @9
    @15
    cc0
    @29
    cX
    @8
    @14
    vk
    @29
    @7
    @13
    cvol
    @29
    @4
    @11
    @6
    @12
    cico
    @27
    @4
    @11
    wceq
    @28
    @2
    @3
    cA
    fveq1
    adantr
    @28
    @6
    @12
    wceq
    @27
    @2
    @5
    cB
    fveq1
    adantl
    oveq12d
    fveq2d
    prodeq2ad
    ifeq2d
    adantl
    wph
    cA
    @0
    wcel
    #
    cX
    cr
    cA
    wf
    #
    hoidmvval.a
    wph
    cr
    cvv
    wcel
    #
    cX
    cfn
    wcel
    #
    @30
    @31
    wb
    @32
    wph
    reex
    a1i
    #
    hoidmvval.x
    cr
    cX
    cA
    cvv
    cfn
    elmapg
    syl2anc
    mpbird
    wph
    cB
    @0
    wcel
    #
    cX
    cr
    cB
    wf
    #
    hoidmvval.b
    wph
    @32
    @33
    @35
    @36
    wb
    @34
    hoidmvval.x
    cr
    cX
    cB
    cvv
    cfn
    elmapg
    syl2anc
    mpbird
    @16
    cvv
    wcel
    wph
    @1
    cc0
    @15
    c0ex
    cX
    @14
    vk
    prodex
    ifex
    a1i
    ovmpt2d
end
