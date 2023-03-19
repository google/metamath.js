include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cplusg.mm"
include "caddc.mm"
include "cphl.mm"
include "wceq.mm"
include "cphphl.mm"
include "eqid.mm"
include "ipdi.mm"
include "sylan.mm"
include "cclm.mm"
include "cphclm.mm"
include "clmadd.mm"
include "syl.mm"
include "adantr.mm"
include "oveqd.mm"
include "eqtr4d.mm"

theorem cphdi
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphdir.P: |- .+ = ( +g ` W )


  assert |- ( ( W e. CPreHil /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( A ., ( B .+ C ) ) = ( ( A ., B ) + ( A ., C ) ) )

  proof
    cW
    ccph
    wcel
    #
    cA
    cV
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
    cC
    c.pl
    co
    c.xi
    co
    #
    cA
    cB
    c.xi
    co
    #
    cA
    cC
    c.xi
    co
    #
    cW
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    @4
    @5
    caddc
    co
    @0
    cW
    cphl
    wcel
    @1
    @3
    @8
    wceq
    cW
    cphphl
    cA
    cB
    cC
    c.pl
    @7
    @6
    c.xi
    cV
    cW
    @6
    eqid
    #
    cphipcj.h
    cphipcj.v
    cphdir.P
    @7
    eqid
    ipdi
    sylan
    @2
    caddc
    @7
    @4
    @5
    @0
    caddc
    @7
    wceq
    #
    @1
    @0
    cW
    cclm
    wcel
    @10
    cW
    cphclm
    @6
    cW
    @9
    clmadd
    syl
    adantr
    oveqd
    eqtr4d
end
