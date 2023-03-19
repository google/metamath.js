include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "ccj.mm"
include "cmul.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "absvalsq.mm"
include "adantr.mm"
include "cr.mm"
include "abscl.mm"
include "recnd.mm"
include "sqvald.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "simpl.mm"
include "cjcld.mm"
include "abs00.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "div23d.mm"
include "divcan3d.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "divcld.mm"
include "cjmuld.mm"
include "cjcjd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cjred.mm"
include "oveq12d.mm"
include "2timesd.mm"
include "eqtr4d.mm"

theorem abslem2
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( ( ( * ` ( A / ( abs ` A ) ) ) x. A ) + ( ( A / ( abs ` A ) ) x. ( * ` A ) ) ) = ( 2 x. ( abs ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    cA
    cabs
    cfv
    #
    cdiv
    co
    #
    ccj
    cfv
    #
    cA
    cmul
    co
    #
    @4
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @3
    @3
    caddc
    co
    c2
    @3
    cmul
    co
    @2
    @6
    @3
    @8
    @3
    caddc
    @2
    @8
    ccj
    cfv
    #
    @3
    ccj
    cfv
    @6
    @3
    @2
    @8
    @3
    ccj
    @2
    cA
    @7
    cmul
    co
    #
    @3
    cdiv
    co
    @3
    @3
    cmul
    co
    #
    @3
    cdiv
    co
    @8
    @3
    @2
    @10
    @11
    @3
    cdiv
    @2
    @3
    c2
    cexp
    co
    #
    @10
    @11
    @0
    @12
    @10
    wceq
    @1
    cA
    absvalsq
    adantr
    @2
    @3
    @2
    @3
    @0
    @3
    cr
    wcel
    @1
    cA
    abscl
    adantr
    #
    recnd
    #
    sqvald
    eqtr3d
    oveq1d
    @2
    cA
    @7
    @3
    @0
    @1
    simpl
    #
    @2
    cA
    @15
    cjcld
    #
    @14
    @0
    @3
    cc0
    wne
    @1
    @0
    @3
    cc0
    cA
    cc0
    cA
    abs00
    necon3bid
    biimpar
    #
    div23d
    @2
    @3
    @3
    @14
    @14
    @17
    divcan3d
    3eqtr3d
    #
    fveq2d
    @2
    @9
    @5
    @7
    ccj
    cfv
    #
    cmul
    co
    @6
    @2
    @4
    @7
    @2
    cA
    @3
    @15
    @14
    @17
    divcld
    @16
    cjmuld
    @2
    @19
    cA
    @5
    cmul
    @2
    cA
    @15
    cjcjd
    oveq2d
    eqtrd
    @2
    @3
    @13
    cjred
    3eqtr3d
    @18
    oveq12d
    @2
    @3
    @14
    2timesd
    eqtr4d
end
