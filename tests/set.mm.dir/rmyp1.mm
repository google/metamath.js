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
include "crmx.mm"
include "cmul.mm"
include "wceq.mm"
include "1z.mm"
include "rmyadd.mm"
include "mp3an3.mm"
include "rmx1.mm"
include "oveq2d.mm"
include "adantr.mm"
include "rmy1.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"

theorem rmyp1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) = ( ( ( A rmY N ) x. A ) + ( A rmX N ) ) )

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
    #
    cA
    cN
    crmy
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
    cN
    crmx
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
    caddc
    co
    #
    @5
    cA
    cmul
    co
    #
    @8
    caddc
    co
    @1
    @2
    c1
    cz
    wcel
    @4
    @11
    wceq
    1z
    cA
    cN
    c1
    rmyadd
    mp3an3
    @3
    @7
    @12
    @10
    @8
    caddc
    @1
    @7
    @12
    wceq
    @2
    @1
    @6
    cA
    @5
    cmul
    cA
    rmx1
    oveq2d
    adantr
    @3
    @10
    @8
    c1
    cmul
    co
    #
    @8
    @1
    @10
    @13
    wceq
    @2
    @1
    @9
    c1
    @8
    cmul
    cA
    rmy1
    oveq2d
    adantr
    @3
    @8
    @3
    @8
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0cnd
    mulid1d
    eqtrd
    oveq12d
    eqtrd
end
