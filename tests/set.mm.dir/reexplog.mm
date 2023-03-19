include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cexp.mm"
include "cc.mm"
include "wceq.mm"
include "relogcl.mm"
include "recnd.mm"
include "efexp.mm"
include "sylan.mm"
include "reeflog.mm"
include "oveq1d.mm"
include "adantr.mm"
include "eqtr2d.mm"

theorem reexplog
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR+ /\ N e. ZZ ) -> ( A ^ N ) = ( exp ` ( N x. ( log ` A ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cN
    cA
    clog
    cfv
    #
    cmul
    co
    ce
    cfv
    #
    @2
    ce
    cfv
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    @0
    @2
    cc
    wcel
    @1
    @3
    @5
    wceq
    @0
    @2
    cA
    relogcl
    recnd
    @2
    cN
    efexp
    sylan
    @0
    @5
    @6
    wceq
    @1
    @0
    @4
    cA
    cN
    cexp
    cA
    reeflog
    oveq1d
    adantr
    eqtr2d
end
