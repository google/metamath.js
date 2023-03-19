include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "simpl.mm"
include "csn.mm"
include "cfn.mm"
include "snfi.mm"
include "matring.mm"
include "sylancr.mm"
include "jca.mm"
include "mat1ghm.mm"
include "eqid.mm"
include "mat1mhm.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem mat1rhm
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
  assert |- ( ( R e. Ring /\ E e. V ) -> F e. ( R RingHom A ) )

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
    @0
    cA
    crg
    wcel
    #
    wa
    cF
    cR
    cA
    cghm
    co
    wcel
    #
    cF
    cR
    cmgp
    cfv
    #
    cA
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    cF
    cR
    cA
    crh
    co
    wcel
    @2
    @0
    @3
    @0
    @1
    simpl
    #
    @2
    cE
    csn
    #
    cfn
    wcel
    @0
    @3
    cE
    snfi
    @8
    cA
    cR
    @9
    mat1rhmval.a
    matring
    sylancr
    jca
    @2
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
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1ghm
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    @5
    @6
    cO
    cV
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    @5
    eqid
    #
    @6
    eqid
    #
    mat1mhm
    jca
    cR
    cA
    cF
    @5
    @6
    @10
    @11
    isrhm
    sylanbrc
end
