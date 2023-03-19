include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crmx.mm"
include "cmul.mm"
include "cexp.mm"
include "cmin.mm"
include "crmy.mm"
include "wceq.mm"
include "1z.mm"
include "rmxadd.mm"
include "mp3an3.mm"
include "rmx1.mm"
include "adantr.mm"
include "oveq2d.mm"
include "rmy1.mm"
include "frmy.mm"
include "fovcl.mm"
include "zcnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"

theorem rmxp1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( N + 1 ) ) = ( ( ( A rmX N ) x. A ) + ( ( ( A ^ 2 ) - 1 ) x. ( A rmY N ) ) ) )

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
    crmx
    co
    #
    cA
    cN
    crmx
    co
    #
    cA
    c1
    crmx
    co
    #
    cmul
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    cA
    cN
    crmy
    co
    #
    cA
    c1
    crmy
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @5
    cA
    cmul
    co
    #
    @8
    @9
    cmul
    co
    #
    caddc
    co
    @1
    @2
    c1
    cz
    wcel
    @4
    @13
    wceq
    1z
    cA
    cN
    c1
    rmxadd
    mp3an3
    @3
    @7
    @14
    @12
    @15
    caddc
    @3
    @6
    cA
    @5
    cmul
    @1
    @6
    cA
    wceq
    @2
    cA
    rmx1
    adantr
    oveq2d
    @3
    @11
    @9
    @8
    cmul
    @3
    @11
    @9
    c1
    cmul
    co
    #
    @9
    @1
    @11
    @16
    wceq
    @2
    @1
    @10
    c1
    @9
    cmul
    cA
    rmy1
    oveq2d
    adantr
    @3
    @9
    @3
    @9
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zcnd
    mulid1d
    eqtrd
    oveq2d
    oveq12d
    eqtrd
end
