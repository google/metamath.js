include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "df-ov.mm"
include "csn.mm"
include "mat1rhmval.mm"
include "fveq1d.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "opex.mm"
include "eqeltri.mm"
include "simp3.mm"
include "fvsng.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem mat1rhmelval
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
  assert |- ( ( R e. Ring /\ E e. V /\ X e. K ) -> ( E ( F ` X ) E ) = X )

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
    cE
    cE
    cX
    cF
    cfv
    #
    co
    cE
    cE
    cop
    #
    @4
    cfv
    #
    cX
    cE
    cE
    @4
    df-ov
    @3
    @6
    @5
    cO
    cX
    cop
    csn
    #
    cfv
    #
    cX
    @3
    @5
    @4
    @7
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
    fveq1d
    @3
    @8
    cO
    @7
    cfv
    #
    cX
    @5
    cO
    @7
    cO
    @5
    mat1rhmval.o
    eqcomi
    fveq2i
    @3
    cO
    cvv
    wcel
    @2
    @9
    cX
    wceq
    cO
    @5
    cvv
    mat1rhmval.o
    cE
    cE
    opex
    eqeltri
    @0
    @1
    @2
    simp3
    cO
    cX
    cvv
    cK
    fvsng
    sylancr
    syl5eq
    eqtrd
    syl5eq
end
