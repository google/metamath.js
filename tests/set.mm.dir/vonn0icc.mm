include "cvoln.mm"
include "cfv.mm"
include "cfn.mm"
include "cr.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "cbvprodv.mm"
include "ifeq2.mm"
include "ax-mp.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "mpteq2i.mm"
include "vonicc.mm"
include "fveq1i.mm"
include "oveqi.mm"
include "eqtrd.mm"
include "eqid.mm"
include "hoidmvn0val.mm"
include "ffvelrnda.mm"
include "voliccico.mm"
include "eqcomd.mm"
include "prodeq2dv.mm"
include "3eqtrd.mm"

theorem vonn0icc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vj: setvar j
  assume vonn0icc.x: |- ( ph -> X e. Fin )
  assume vonn0icc.n: |- ( ph -> X =/= (/) )
  assume vonn0icc.a: |- ( ph -> A : X --> RR )
  assume vonn0icc.b: |- ( ph -> B : X --> RR )
  assume vonn0icc.i: |- I = X_ k e. X ( ( A ` k ) [,] ( B ` k ) )

  disjoint A k
  disjoint B k
  disjoint X k
  disjoint k ph
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a j
  disjoint b j
  disjoint j k
  disjoint j x
  disjoint a ph
  disjoint b ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( voln ` X ) ` I ) = prod_ k e. X ( vol ` ( ( A ` k ) [,] ( B ` k ) ) ) )

  proof
    wph
    cI
    cX
    cvoln
    cfv
    cfv
    #
    cA
    cB
    cX
    vx
    cfn
    va
    vb
    cr
    vx
    cv
    #
    cmap
    co
    #
    @2
    @1
    c0
    wceq
    #
    cc0
    @1
    vk
    cv
    #
    va
    cv
    #
    cfv
    #
    @4
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
    cmpt2
    #
    cmpt
    #
    cfv
    #
    co
    #
    cX
    @4
    cA
    cfv
    #
    @4
    cB
    cfv
    #
    cico
    co
    cvol
    cfv
    #
    vk
    cprod
    cX
    @17
    @18
    cicc
    co
    cvol
    cfv
    #
    vk
    cprod
    wph
    @0
    cA
    cB
    cX
    vx
    cfn
    va
    vb
    @2
    @2
    @3
    cc0
    @1
    vj
    cv
    #
    @5
    cfv
    #
    @21
    @7
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vj
    cprod
    #
    cif
    #
    cmpt2
    #
    cmpt
    #
    cfv
    #
    co
    #
    @16
    wph
    vx
    cA
    cB
    vk
    cI
    @29
    cX
    va
    vb
    vonn0icc.x
    vonn0icc.a
    vonn0icc.b
    vonn0icc.i
    vx
    cfn
    @28
    @13
    va
    vb
    @2
    @2
    @27
    @12
    @27
    @12
    wceq
    #
    @5
    @2
    wcel
    @7
    @2
    wcel
    wa
    @26
    @11
    wceq
    @32
    @1
    @25
    @10
    vj
    vk
    @21
    @4
    wceq
    #
    @24
    @9
    cvol
    @33
    @22
    @6
    @23
    @8
    cico
    @21
    @4
    @5
    fveq2
    @21
    @4
    @7
    fveq2
    oveq12d
    fveq2d
    cbvprodv
    @3
    @26
    @11
    cc0
    ifeq2
    ax-mp
    a1i
    mpt2eq3ia
    mpteq2i
    #
    vonicc
    @31
    @16
    wceq
    wph
    @30
    @15
    cA
    cB
    cX
    @29
    @14
    @34
    fveq1i
    oveqi
    a1i
    eqtrd
    wph
    vx
    cA
    cB
    vk
    @14
    cX
    va
    vb
    @14
    eqid
    vonn0icc.x
    vonn0icc.n
    vonn0icc.a
    vonn0icc.b
    hoidmvn0val
    wph
    cX
    @19
    @20
    vk
    wph
    @4
    cX
    wcel
    wa
    #
    @20
    @19
    @35
    @17
    @18
    wph
    cX
    cr
    @4
    cA
    vonn0icc.a
    ffvelrnda
    wph
    cX
    cr
    @4
    cB
    vonn0icc.b
    ffvelrnda
    voliccico
    eqcomd
    prodeq2dv
    3eqtrd
end
