include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "relogexp.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "relogcl.mm"
include "recnd.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "cc0.mm"
include "logne0.mm"
include "divassd.mm"
include "eqtrd.mm"

theorem reglogexp
  let cA: class A
  let cC: class C
  let cN: class N


  assert |- ( ( A e. RR+ /\ N e. ZZ /\ ( C e. RR+ /\ C =/= 1 ) ) -> ( ( log ` ( A ^ N ) ) / ( log ` C ) ) = ( N x. ( ( log ` A ) / ( log ` C ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cN
    cz
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
    cN
    cexp
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
    cN
    cA
    clog
    cfv
    #
    cmul
    co
    #
    @7
    cdiv
    co
    cN
    @8
    @7
    cdiv
    co
    cmul
    co
    @5
    @6
    @9
    @7
    cdiv
    @0
    @1
    @6
    @9
    wceq
    @4
    cA
    cN
    relogexp
    3adant3
    oveq1d
    @5
    cN
    @8
    @7
    @1
    @0
    cN
    cc
    wcel
    @4
    cN
    zcn
    3ad2ant2
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
    @4
    @0
    @7
    cc
    wcel
    #
    @1
    @2
    @10
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
    divassd
    eqtrd
end
