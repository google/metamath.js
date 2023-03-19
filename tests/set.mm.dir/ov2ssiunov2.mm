include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wrex.mm"
include "simp3.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "rspcedv.mm"
include "wi.mm"
include "eliunov2.mm"
include "biimprd.mm"
include "3adant3.mm"
include "syld.mm"
include "ssrdv.mm"

theorem ov2ssiunov2
  let cC: class C
  let cR: class R
  let cU: class U
  let vn: setvar n
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vx: setvar x
  assume ov2ssiunov2.def: |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) )

  disjoint M n
  disjoint R r
  disjoint R n
  disjoint U n
  disjoint V n
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
  disjoint .^ x
  disjoint C x
  disjoint n x
  disjoint M x
  disjoint N x
  disjoint R x
  disjoint U x
  disjoint V x
  assert |- ( ( R e. U /\ N e. V /\ M e. N ) -> ( R .^ M ) C_ ( C ` R ) )

  proof
    cR
    cU
    wcel
    #
    cN
    cV
    wcel
    #
    cM
    cN
    wcel
    #
    w3a
    #
    vx
    cR
    cM
    c.ex
    co
    #
    cR
    cC
    cfv
    #
    @3
    vx
    cv
    #
    @4
    wcel
    #
    @6
    cR
    vn
    cv
    #
    c.ex
    co
    #
    wcel
    #
    vn
    cN
    wrex
    #
    @6
    @5
    wcel
    #
    @3
    @10
    @7
    vn
    cM
    cN
    @0
    @1
    @2
    simp3
    @3
    @8
    cM
    wceq
    #
    wa
    #
    @9
    @4
    @6
    @14
    @8
    cM
    cR
    c.ex
    @3
    @13
    simpr
    oveq2d
    eleq2d
    rspcedv
    @0
    @1
    @11
    @12
    wi
    @2
    @0
    @1
    wa
    @12
    @11
    cC
    cR
    cU
    vn
    c.ex
    cN
    cV
    @6
    vr
    ov2ssiunov2.def
    eliunov2
    biimprd
    3adant3
    syld
    ssrdv
end
