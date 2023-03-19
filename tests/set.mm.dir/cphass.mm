include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmul.mm"
include "cphl.mm"
include "wceq.mm"
include "cphphl.mm"
include "eqid.mm"
include "ipass.mm"
include "sylan.mm"
include "cclm.mm"
include "cphclm.mm"
include "clmmul.mm"
include "syl.mm"
include "adantr.mm"
include "oveqd.mm"
include "eqtr4d.mm"

theorem cphass
  let cA: class A
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphass.f: |- F = ( Scalar ` W )
  assume cphass.k: |- K = ( Base ` F )
  assume cphass.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CPreHil /\ ( A e. K /\ B e. V /\ C e. V ) ) -> ( ( A .x. B ) ., C ) = ( A x. ( B ., C ) ) )

  proof
    cW
    ccph
    wcel
    #
    cA
    cK
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    #
    wa
    #
    cA
    cB
    c.x
    co
    cC
    c.xi
    co
    #
    cA
    cB
    cC
    c.xi
    co
    #
    cF
    cmulr
    cfv
    #
    co
    #
    cA
    @4
    cmul
    co
    @0
    cW
    cphl
    wcel
    @1
    @3
    @6
    wceq
    cW
    cphphl
    cA
    cB
    cC
    c.x
    @5
    cF
    c.xi
    cK
    cV
    cW
    cphass.f
    cphipcj.h
    cphipcj.v
    cphass.k
    cphass.s
    @5
    eqid
    ipass
    sylan
    @2
    cmul
    @5
    cA
    @4
    @0
    cmul
    @5
    wceq
    #
    @1
    @0
    cW
    cclm
    wcel
    @7
    cW
    cphclm
    cF
    cW
    cphass.f
    clmmul
    syl
    adantr
    oveqd
    eqtr4d
end
