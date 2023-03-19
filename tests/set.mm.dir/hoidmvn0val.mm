include "cfv.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cif.mm"
include "hoidmvval.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem hoidmvn0val
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume hoidmvn0val.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvn0val.x: |- ( ph -> X e. Fin )
  assume hoidmvn0val.n: |- ( ph -> X =/= (/) )
  assume hoidmvn0val.a: |- ( ph -> A : X --> RR )
  assume hoidmvn0val.b: |- ( ph -> B : X --> RR )

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
  assert |- ( ph -> ( A ( L ` X ) B ) = prod_ k e. X ( vol ` ( ( A ` k ) [,) ( B ` k ) ) ) )

  proof
    wph
    cA
    cB
    cX
    cL
    cfv
    co
    cX
    c0
    wceq
    #
    cc0
    cX
    vk
    cv
    #
    cA
    cfv
    @1
    cB
    cfv
    cico
    co
    cvol
    cfv
    vk
    cprod
    #
    cif
    @2
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hoidmvn0val.l
    hoidmvn0val.a
    hoidmvn0val.b
    hoidmvn0val.x
    hoidmvval
    wph
    @0
    cc0
    @2
    wph
    cX
    c0
    hoidmvn0val.n
    neneqd
    iffalsed
    eqtrd
end
