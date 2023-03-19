include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "crh.mm"
include "wf1o.mm"
include "mat1rhm.mm"
include "mat1f1o.mm"
include "wb.mm"
include "csn.mm"
include "cfn.mm"
include "snfi.mm"
include "simpl.mm"
include "matring.mm"
include "sylancr.mm"
include "isrim.mm"
include "syldan.mm"
include "mpbir2and.mm"

theorem mat1rngiso
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
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let vy: setvar y
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
  disjoint A x
  disjoint F x
  disjoint X x
  disjoint A i
  disjoint A j
  disjoint A w
  disjoint A y
  disjoint i j
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint B w
  disjoint B y
  disjoint E i
  disjoint E j
  disjoint E w
  disjoint E y
  disjoint F i
  disjoint F j
  disjoint F w
  disjoint F y
  disjoint K w
  disjoint K y
  disjoint R i
  disjoint R j
  disjoint R w
  disjoint R y
  disjoint V w
  disjoint V y
  assert |- ( ( R e. Ring /\ E e. V ) -> F e. ( R RingIso A ) )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cF
    cR
    cA
    crs
    co
    wcel
    #
    cF
    cR
    cA
    crh
    co
    wcel
    #
    cK
    cB
    cF
    wf1o
    #
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
    mat1rhm
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
    @0
    @1
    cA
    crg
    wcel
    #
    @3
    @4
    @5
    wa
    wb
    @2
    cE
    csn
    #
    cfn
    wcel
    @0
    @6
    cE
    snfi
    @0
    @1
    simpl
    cA
    cR
    @7
    mat1rhmval.a
    matring
    sylancr
    cK
    cB
    cR
    cA
    cF
    crg
    crg
    mat1rhmval.k
    mat1rhmval.b
    isrim
    syldan
    mpbir2and
end
