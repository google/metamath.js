include "ccph.mm"
include "wcel.mm"
include "ci.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp3.mm"
include "simp2.mm"
include "cphass.mm"
include "syl13anc.mm"

theorem cphassi
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cW: class W
  let cX: class X
  assume cphassi.x: |- X = ( Base ` W )
  assume cphassi.s: |- .x. = ( .s ` W )
  assume cphassi.i: |- ., = ( .i ` W )
  assume cphassi.f: |- F = ( Scalar ` W )
  assume cphassi.k: |- K = ( Base ` F )


  assert |- ( ( ( W e. CPreHil /\ _i e. K ) /\ A e. X /\ B e. X ) -> ( ( _i .x. B ) ., A ) = ( _i x. ( B ., A ) ) )

  proof
    cW
    ccph
    wcel
    #
    ci
    cK
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    @0
    @1
    @4
    @3
    ci
    cB
    c.x
    co
    cA
    c.xi
    co
    ci
    cB
    cA
    c.xi
    co
    cmul
    co
    wceq
    @0
    @1
    @3
    @4
    simp1l
    @0
    @1
    @3
    @4
    simp1r
    @2
    @3
    @4
    simp3
    @2
    @3
    @4
    simp2
    ci
    cB
    cA
    c.x
    cF
    c.xi
    cK
    cX
    cW
    cphassi.i
    cphassi.x
    cphassi.f
    cphassi.k
    cphassi.s
    cphass
    syl13anc
end
