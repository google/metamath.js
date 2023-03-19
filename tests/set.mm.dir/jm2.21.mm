include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cmul.mm"
include "co.mm"
include "crmx.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "crmy.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "rmbaserp.mm"
include "rpcnne0d.mm"
include "expmulz.mm"
include "sylan.mm"
include "zmulcl.mm"
include "rmxyval.mm"
include "sylan2.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "3impb.mm"

theorem jm2.21
  let cA: class A
  let cJ: class J
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ J e. ZZ ) -> ( ( A rmX ( N x. J ) ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY ( N x. J ) ) ) ) = ( ( ( A rmX N ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( A rmY N ) ) ) ^ J ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cJ
    cz
    wcel
    #
    cA
    cN
    cJ
    cmul
    co
    #
    crmx
    co
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    csqrt
    cfv
    #
    cA
    @3
    crmy
    co
    cmul
    co
    caddc
    co
    #
    cA
    cN
    crmx
    co
    @4
    cA
    cN
    crmy
    co
    cmul
    co
    caddc
    co
    #
    cJ
    cexp
    co
    #
    wceq
    @0
    @1
    @2
    wa
    #
    wa
    #
    cA
    @4
    caddc
    co
    #
    @3
    cexp
    co
    #
    @10
    cN
    cexp
    co
    #
    cJ
    cexp
    co
    #
    @5
    @7
    @0
    @10
    cc
    wcel
    @10
    cc0
    wne
    wa
    @8
    @11
    @13
    wceq
    @0
    @10
    cA
    rmbaserp
    rpcnne0d
    @10
    cN
    cJ
    expmulz
    sylan
    @8
    @0
    @3
    cz
    wcel
    @5
    @11
    wceq
    cN
    cJ
    zmulcl
    cA
    @3
    rmxyval
    sylan2
    @9
    @6
    @12
    cJ
    cexp
    @0
    @1
    @6
    @12
    wceq
    @2
    cA
    cN
    rmxyval
    adantrr
    oveq1d
    3eqtr4d
    3impb
end
