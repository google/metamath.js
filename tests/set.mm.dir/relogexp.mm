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
include "eqtrd.mm"
include "fveq2d.mm"
include "cr.mm"
include "zre.mm"
include "remulcl.mm"
include "syl2anr.mm"
include "relogef.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem relogexp
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR+ /\ N e. ZZ ) -> ( log ` ( A ^ N ) ) = ( N x. ( log ` A ) ) )

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
    #
    cN
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    clog
    cfv
    #
    cA
    cN
    cexp
    co
    #
    clog
    cfv
    @4
    @2
    @5
    @7
    clog
    @2
    @5
    @3
    ce
    cfv
    #
    cN
    cexp
    co
    #
    @7
    @0
    @3
    cc
    wcel
    @1
    @5
    @9
    wceq
    @0
    @3
    cA
    relogcl
    #
    recnd
    @3
    cN
    efexp
    sylan
    @0
    @9
    @7
    wceq
    @1
    @0
    @8
    cA
    cN
    cexp
    cA
    reeflog
    oveq1d
    adantr
    eqtrd
    fveq2d
    @2
    @4
    cr
    wcel
    #
    @6
    @4
    wceq
    @1
    cN
    cr
    wcel
    @3
    cr
    wcel
    @11
    @0
    cN
    zre
    @10
    cN
    @3
    remulcl
    syl2anr
    @4
    relogef
    syl
    eqtr3d
end
