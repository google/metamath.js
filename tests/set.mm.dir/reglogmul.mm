include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "caddc.mm"
include "wceq.mm"
include "relogmul.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "cc.mm"
include "relogcl.mm"
include "recnd.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "cc0.mm"
include "logne0.mm"
include "divdird.mm"
include "eqtrd.mm"

theorem reglogmul
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR+ /\ B e. RR+ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( ( log ` ( A x. B ) ) / ( log ` C ) ) = ( ( ( log ` A ) / ( log ` C ) ) + ( ( log ` B ) / ( log ` C ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    cC
    crp
    wcel
    #
    cC
    c1
    wne
    #
    wa
    #
    w3a
    #
    cA
    cB
    cmul
    co
    clog
    cfv
    #
    cC
    clog
    cfv
    #
    cdiv
    co
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    caddc
    co
    #
    @7
    cdiv
    co
    @8
    @7
    cdiv
    co
    @9
    @7
    cdiv
    co
    caddc
    co
    @5
    @6
    @10
    @7
    cdiv
    @0
    @1
    @6
    @10
    wceq
    @4
    cA
    cB
    relogmul
    3adant3
    oveq1d
    @5
    @8
    @9
    @7
    @0
    @1
    @8
    cc
    wcel
    @4
    @0
    @8
    cA
    relogcl
    recnd
    3ad2ant1
    @1
    @0
    @9
    cc
    wcel
    @4
    @1
    @9
    cB
    relogcl
    recnd
    3ad2ant2
    @4
    @0
    @7
    cc
    wcel
    #
    @1
    @2
    @11
    @3
    @2
    @7
    cC
    relogcl
    recnd
    adantr
    3ad2ant3
    @4
    @0
    @7
    cc0
    wne
    @1
    cC
    logne0
    3ad2ant3
    divdird
    eqtrd
end
