include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crmy.mm"
include "cmul.mm"
include "cmin.mm"
include "rmyluc.mm"
include "frmy.mm"
include "fovcl.mm"
include "zcnd.mm"
include "cc.mm"
include "eluzelcn.mm"
include "adantr.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem rmyluc2
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) = ( ( ( 2 x. A ) x. ( A rmY N ) ) - ( A rmY ( N - 1 ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    c1
    caddc
    co
    crmy
    co
    c2
    cA
    cN
    crmy
    co
    #
    cA
    cmul
    co
    #
    cmul
    co
    #
    cA
    cN
    c1
    cmin
    co
    crmy
    co
    #
    cmin
    co
    c2
    cA
    cmul
    co
    @4
    cmul
    co
    #
    @7
    cmin
    co
    cA
    cN
    rmyluc
    @3
    @6
    @8
    @7
    cmin
    @3
    @6
    c2
    cA
    @4
    cmul
    co
    #
    cmul
    co
    @8
    @3
    @5
    @9
    c2
    cmul
    @3
    @4
    cA
    @3
    @4
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zcnd
    #
    @1
    cA
    cc
    wcel
    @2
    c2
    cA
    eluzelcn
    adantr
    #
    mulcomd
    oveq2d
    @3
    c2
    cA
    @4
    @3
    2cnd
    @11
    @10
    mulassd
    eqtr4d
    oveq1d
    eqtrd
end
