include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "ccj.mm"
include "cmul.mm"
include "csqrt.mm"
include "cc.mm"
include "wceq.mm"
include "cphipcl.mm"
include "absval.mm"
include "syl.mm"
include "oveq1d.mm"
include "cjcld.mm"
include "mulcld.mm"
include "sqsqrtd.mm"
include "cphipcj.mm"
include "oveq2d.mm"
include "3eqtrrd.mm"

theorem cphipipcj
  let cA: class A
  let cB: class B
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )


  assert |- ( ( W e. CPreHil /\ A e. V /\ B e. V ) -> ( ( A ., B ) x. ( B ., A ) ) = ( ( abs ` ( A ., B ) ) ^ 2 ) )

  proof
    cW
    ccph
    wcel
    cA
    cV
    wcel
    cB
    cV
    wcel
    w3a
    #
    cA
    cB
    c.xi
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    @1
    @1
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    c2
    cexp
    co
    @4
    @1
    cB
    cA
    c.xi
    co
    #
    cmul
    co
    @0
    @2
    @5
    c2
    cexp
    @0
    @1
    cc
    wcel
    @2
    @5
    wceq
    cA
    cB
    c.xi
    cV
    cW
    cphipcj.v
    cphipcj.h
    cphipcl
    #
    @1
    absval
    syl
    oveq1d
    @0
    @4
    @0
    @1
    @3
    @7
    @0
    @1
    @7
    cjcld
    mulcld
    sqsqrtd
    @0
    @3
    @6
    @1
    cmul
    cA
    cB
    c.xi
    cV
    cW
    cphipcj.h
    cphipcj.v
    cphipcj
    oveq2d
    3eqtrrd
end
