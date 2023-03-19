include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "wf.mm"
include "mat1f1o.mm"
include "f1of.mm"
include "syl.mm"

theorem mat1f
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
  disjoint B x
  disjoint X x
  assert |- ( ( R e. Ring /\ E e. V ) -> F : K --> B )

  proof
    cR
    crg
    wcel
    cE
    cV
    wcel
    wa
    cK
    cB
    cF
    wf1o
    cK
    cB
    cF
    wf
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1f1o
    cK
    cB
    cF
    f1of
    syl
end
