include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
include "cdiv.mm"
include "wceq.mm"
include "cmul.mm"
include "cjcl.mm"
include "adantr.mm"
include "simpl.mm"
include "mulcomd.mm"
include "absvalsq.mm"
include "eqtr4d.mm"
include "cr.mm"
include "abscl.mm"
include "recnd.mm"
include "sqcld.mm"
include "cjne0.mm"
include "biimpa.mm"
include "divmuld.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "abs00.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "recdivd.mm"
include "eqtr3d.mm"

theorem recval
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( 1 / A ) = ( ( * ` A ) / ( ( abs ` A ) ^ 2 ) ) )

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
    c1
    cA
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cA
    ccj
    cfv
    #
    cdiv
    co
    #
    cdiv
    co
    c1
    cA
    cdiv
    co
    @5
    @4
    cdiv
    co
    @2
    @6
    cA
    c1
    cdiv
    @2
    @6
    cA
    wceq
    @5
    cA
    cmul
    co
    #
    @4
    wceq
    @2
    @7
    cA
    @5
    cmul
    co
    #
    @4
    @2
    @5
    cA
    @0
    @5
    cc
    wcel
    @1
    cA
    cjcl
    adantr
    #
    @0
    @1
    simpl
    #
    mulcomd
    @0
    @4
    @8
    wceq
    @1
    cA
    absvalsq
    adantr
    eqtr4d
    @2
    @4
    @5
    cA
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
    recnd
    #
    sqcld
    #
    @9
    @10
    @0
    @1
    @5
    cc0
    wne
    cA
    cjne0
    biimpa
    #
    divmuld
    mpbird
    oveq2d
    @2
    @4
    @5
    @12
    @9
    @2
    @4
    cc0
    wne
    #
    @3
    cc0
    wne
    #
    @0
    @15
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
    @2
    @3
    cc
    wcel
    @14
    @15
    wb
    @11
    @3
    sqne0
    syl
    mpbird
    @13
    recdivd
    eqtr3d
end
