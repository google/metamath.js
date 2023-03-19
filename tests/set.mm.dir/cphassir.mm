include "ccph.mm"
include "wcel.mm"
include "ci.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cneg.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2.mm"
include "simp3.mm"
include "cphassr.mm"
include "syl13anc.mm"
include "cji.mm"
include "oveq1i.mm"
include "syl6eq.mm"

theorem cphassir
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


  assert |- ( ( ( W e. CPreHil /\ _i e. K ) /\ A e. X /\ B e. X ) -> ( A ., ( _i .x. B ) ) = ( -u _i x. ( A ., B ) ) )

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
    #
    cA
    ci
    cB
    c.x
    co
    c.xi
    co
    #
    ci
    ccj
    cfv
    #
    cA
    cB
    c.xi
    co
    #
    cmul
    co
    #
    ci
    cneg
    #
    @8
    cmul
    co
    @5
    @0
    @1
    @3
    @4
    @6
    @9
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
    simp2
    @2
    @3
    @4
    simp3
    ci
    cA
    cB
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
    cphassr
    syl13anc
    @7
    @10
    @8
    cmul
    cji
    oveq1i
    syl6eq
end
