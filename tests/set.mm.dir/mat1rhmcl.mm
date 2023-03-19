include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cbs.mm"
include "cfv.mm"
include "mat1dimbas.mm"
include "mat1rhmval.mm"
include "wceq.mm"
include "a1i.mm"
include "3eltr4d.mm"

theorem mat1rhmcl
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cX: class X
  assume mat1rhmval.k: |- K = ( Base ` R )
  assume mat1rhmval.a: |- A = ( { E } Mat R )
  assume mat1rhmval.b: |- B = ( Base ` A )
  assume mat1rhmval.o: |- O = <. E , E >.
  assume mat1rhmval.f: |- F = ( x e. K |-> { <. O , x >. } )

  disjoint K x
  disjoint O x
  disjoint E x
  disjoint R x
  disjoint V x
  disjoint X x
  assert |- ( ( R e. Ring /\ E e. V /\ X e. K ) -> ( F ` X ) e. B )

  proof
    cR
    crg
    wcel
    cE
    cV
    wcel
    cX
    cK
    wcel
    w3a
    #
    cO
    cX
    cop
    csn
    cA
    cbs
    cfv
    #
    cX
    cF
    cfv
    cB
    cA
    cK
    cR
    cE
    cO
    cV
    cX
    mat1rhmval.a
    mat1rhmval.k
    mat1rhmval.o
    mat1dimbas
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    cX
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmval
    cB
    @1
    wceq
    @0
    mat1rhmval.b
    a1i
    3eltr4d
end
