include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "wa.mm"
include "simpr.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "briunov2.mm"
include "syldan.mm"

theorem briunov2uz
  let cC: class C
  let cR: class R
  let cU: class U
  let vn: setvar n
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  assume briunov2uz.def: |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) )

  disjoint n r
  disjoint R n
  disjoint R r
  disjoint X n
  disjoint Y n
  disjoint n r
  disjoint C n
  disjoint N n
  disjoint .^ n
  disjoint C r
  disjoint N r
  disjoint .^ r
  disjoint C N
  disjoint .^ C
  disjoint .^ N
  assert |- ( ( R e. U /\ N = ( ZZ>= ` M ) ) -> ( X ( C ` R ) Y <-> E. n e. N X ( R .^ n ) Y ) )

  proof
    cR
    cU
    wcel
    #
    cN
    cM
    cuz
    cfv
    #
    wceq
    #
    cN
    cvv
    wcel
    cX
    cY
    cR
    cC
    cfv
    wbr
    cX
    cY
    cR
    vn
    cv
    c.ex
    co
    wbr
    vn
    cN
    wrex
    wb
    @0
    @2
    wa
    cN
    @1
    cvv
    @0
    @2
    simpr
    cM
    cuz
    fvex
    syl6eqel
    cC
    cR
    cU
    vn
    c.ex
    cN
    cvv
    cX
    cY
    vr
    briunov2uz.def
    briunov2
    syldan
end
