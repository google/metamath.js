include "wcel.mm"
include "wceq.mm"
include "cfv.mm"
include "fveq2.mm"
include "cv.mm"
include "cif.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "anidms.mm"
include "sylan9eqr.mm"
include "ex.mm"

theorem symgextfve
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint X x
  assert |- ( K e. N -> ( X = K -> ( E ` X ) = K ) )

  proof
    cK
    cN
    wcel
    #
    cX
    cK
    wceq
    #
    cX
    cE
    cfv
    #
    cK
    wceq
    @1
    @0
    @2
    cK
    cE
    cfv
    #
    cK
    cX
    cK
    cE
    fveq2
    @0
    @3
    cK
    wceq
    vx
    cK
    vx
    cv
    #
    cK
    wceq
    #
    cK
    @4
    cZ
    cfv
    #
    cif
    cK
    cN
    cN
    cE
    @5
    cK
    @6
    iftrue
    symgext.e
    fvmptg
    anidms
    sylan9eqr
    ex
end
