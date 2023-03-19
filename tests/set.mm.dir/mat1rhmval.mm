include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "opeq2.mm"
include "sneqd.mm"
include "adantl.mm"
include "simp3.mm"
include "snex.mm"
include "fvmptd.mm"

theorem mat1rhmval
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
  assert |- ( ( R e. Ring /\ E e. V /\ X e. K ) -> ( F ` X ) = { <. O , X >. } )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    cX
    cK
    wcel
    #
    w3a
    #
    vx
    cX
    cO
    vx
    cv
    #
    cop
    #
    csn
    #
    cO
    cX
    cop
    #
    csn
    #
    cK
    cF
    cvv
    cF
    vx
    cK
    @6
    cmpt
    wceq
    @3
    mat1rhmval.f
    a1i
    @4
    cX
    wceq
    #
    @6
    @8
    wceq
    @3
    @9
    @5
    @7
    @4
    cX
    cO
    opeq2
    sneqd
    adantl
    @0
    @1
    @2
    simp3
    @8
    cvv
    wcel
    @3
    @7
    snex
    a1i
    fvmptd
end
