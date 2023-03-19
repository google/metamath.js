include "c0.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cif.mm"
include "cfn.mm"
include "wcel.mm"
include "0fin.mm"
include "a1i.mm"
include "hoidmvval.mm"
include "eqid.mm"
include "iftrue.mm"
include "ax-mp.mm"
include "eqtrd.mm"

theorem hoidmv0val
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cL: class L
  let va: setvar a
  let vb: setvar b
  assume hoidmv0val.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmv0val.a: |- ( ph -> A : (/) --> RR )
  assume hoidmv0val.b: |- ( ph -> B : (/) --> RR )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint a ph
  disjoint a x
  disjoint b ph
  disjoint b x
  disjoint ph x
  disjoint k x
  disjoint k x
  assert |- ( ph -> ( A ( L ` (/) ) B ) = 0 )

  proof
    wph
    cA
    cB
    c0
    cL
    cfv
    co
    c0
    c0
    wceq
    #
    cc0
    c0
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
    #
    cc0
    wph
    vx
    cA
    cB
    vk
    cL
    c0
    va
    vb
    hoidmv0val.l
    hoidmv0val.a
    hoidmv0val.b
    c0
    cfn
    wcel
    wph
    0fin
    a1i
    hoidmvval
    @3
    cc0
    wceq
    #
    wph
    @0
    @4
    c0
    eqid
    @0
    cc0
    @2
    iftrue
    ax-mp
    a1i
    eqtrd
end
