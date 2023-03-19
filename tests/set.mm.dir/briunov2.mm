include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wbr.mm"
include "eliunov2.mm"
include "df-br.mm"
include "rexbii.mm"
include "3bitr4g.mm"

theorem briunov2
  let cC: class C
  let cR: class R
  let cU: class U
  let vn: setvar n
  let c.ex: class .^
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  assume briunov2.def: |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) )

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
  assert |- ( ( R e. U /\ N e. V ) -> ( X ( C ` R ) Y <-> E. n e. N X ( R .^ n ) Y ) )

  proof
    cR
    cU
    wcel
    cN
    cV
    wcel
    wa
    cX
    cY
    cop
    #
    cR
    cC
    cfv
    #
    wcel
    @0
    cR
    vn
    cv
    c.ex
    co
    #
    wcel
    #
    vn
    cN
    wrex
    cX
    cY
    @1
    wbr
    cX
    cY
    @2
    wbr
    #
    vn
    cN
    wrex
    cC
    cR
    cU
    vn
    c.ex
    cN
    cV
    @0
    vr
    briunov2.def
    eliunov2
    cX
    cY
    @1
    df-br
    @4
    @3
    vn
    cN
    cX
    cY
    @2
    df-br
    rexbii
    3bitr4g
end
