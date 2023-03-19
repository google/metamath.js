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
include "vonioo.mm"
include "fveq1i.mm"
include "oveqi.mm"
include "eqtrd.mm"
include "eqid.mm"
include "hoidmvn0val.mm"

theorem vonn0ioo
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
  assume vonn0ioo.x: |- ( ph -> X e. Fin )
  assume vonn0ioo.n: |- ( ph -> X =/= (/) )
  assume vonn0ioo.a: |- ( ph -> A : X --> RR )
  assume vonn0ioo.b: |- ( ph -> B : X --> RR )
  assume vonn0ioo.i: |- I = X_ k e. X ( ( A ` k ) (,) ( B ` k ) )

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
  assert |- ( ph -> ( ( voln ` X ) ` I ) = prod_ k e. X ( vol ` ( ( A ` k ) [,) ( B ` k ) ) ) )

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
    @4
    cB
    cfv
    cico
    co
    cvol
    cfv
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
    @17
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
    @25
    cX
    va
    vb
    vonn0ioo.x
    vonn0ioo.a
    vonn0ioo.b
    vonn0ioo.i
    vx
    cfn
    @24
    @13
    va
    vb
    @2
    @2
    @23
    @12
    @23
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
    @22
    @11
    wceq
    @28
    @1
    @21
    @10
    vj
    vk
    @17
    @4
    wceq
    #
    @20
    @9
    cvol
    @29
    @18
    @6
    @19
    @8
    cico
    @17
    @4
    @5
    fveq2
    @17
    @4
    @7
    fveq2
    oveq12d
    fveq2d
    cbvprodv
    @3
    @22
    @11
    cc0
    ifeq2
    ax-mp
    a1i
    mpt2eq3ia
    mpteq2i
    #
    vonioo
    @27
    @16
    wceq
    wph
    @26
    @15
    cA
    cB
    cX
    @25
    @14
    @30
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
    vonn0ioo.x
    vonn0ioo.n
    vonn0ioo.a
    vonn0ioo.b
    hoidmvn0val
    eqtrd
end
