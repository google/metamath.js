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
include "eqid.mm"
include "vonhoi.mm"
include "hoidmvn0val.mm"
include "eqtrd.mm"

theorem vonn0hoi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume vonn0hoi.x: |- ( ph -> X e. Fin )
  assume vonn0hoi.n: |- ( ph -> X =/= (/) )
  assume vonn0hoi.a: |- ( ph -> A : X --> RR )
  assume vonn0hoi.b: |- ( ph -> B : X --> RR )
  assume vonn0hoi.i: |- I = X_ k e. X ( ( A ` k ) [,) ( B ` k ) )

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
    @1
    @0
    c0
    wceq
    cc0
    @0
    vk
    cv
    #
    va
    cv
    cfv
    @2
    vb
    cv
    cfv
    cico
    co
    cvol
    cfv
    vk
    cprod
    cif
    cmpt2
    cmpt
    #
    cfv
    co
    cX
    @2
    cA
    cfv
    @2
    cB
    cfv
    cico
    co
    cvol
    cfv
    vk
    cprod
    wph
    vx
    cA
    cB
    vk
    cI
    @3
    cX
    va
    vb
    vonn0hoi.x
    vonn0hoi.a
    vonn0hoi.b
    vonn0hoi.i
    @3
    eqid
    #
    vonhoi
    wph
    vx
    cA
    cB
    vk
    @3
    cX
    va
    vb
    @4
    vonn0hoi.x
    vonn0hoi.n
    vonn0hoi.a
    vonn0hoi.b
    hoidmvn0val
    eqtrd
end
