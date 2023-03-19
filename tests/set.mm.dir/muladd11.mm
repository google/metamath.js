include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "mpan.mm"
include "adddi.mm"
include "mp3an2.mm"
include "sylan.mm"
include "mulid1d.mm"
include "adantr.mm"
include "adddir.mm"
include "mp3an1.mm"
include "mulid2.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"

theorem muladd11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( 1 + A ) x. ( 1 + B ) ) = ( ( 1 + A ) + ( B + ( A x. B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    c1
    cA
    caddc
    co
    #
    c1
    cB
    caddc
    co
    cmul
    co
    #
    @3
    c1
    cmul
    co
    #
    @3
    cB
    cmul
    co
    #
    caddc
    co
    #
    @3
    cB
    cA
    cB
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @0
    @3
    cc
    wcel
    #
    @1
    @4
    @7
    wceq
    #
    c1
    cc
    wcel
    #
    @0
    @10
    ax-1cn
    c1
    cA
    addcl
    mpan
    #
    @10
    @12
    @1
    @11
    ax-1cn
    @3
    c1
    cB
    adddi
    mp3an2
    sylan
    @2
    @5
    @3
    @6
    @9
    caddc
    @0
    @5
    @3
    wceq
    @1
    @0
    @3
    @13
    mulid1d
    adantr
    @2
    @6
    c1
    cB
    cmul
    co
    #
    @8
    caddc
    co
    #
    @9
    @12
    @0
    @1
    @6
    @15
    wceq
    ax-1cn
    c1
    cA
    cB
    adddir
    mp3an1
    @2
    @14
    cB
    @8
    caddc
    @1
    @14
    cB
    wceq
    @0
    cB
    mulid2
    adantl
    oveq1d
    eqtrd
    oveq12d
    eqtrd
end
