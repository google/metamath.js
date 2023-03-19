include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "fconst6g.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "simpr2.mm"
include "fvconst2g.mm"
include "syldan.mm"
include "3ad2antr1.mm"
include "oveq12d.mm"
include "subid.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simpr1.mm"
include "subcld.mm"
include "simpr3.mm"
include "subne0d.mm"
include "div0d.mm"
include "0cn.mm"
include "dvidlem.mm"

theorem dvconst
  let cA: class A
  let vx: setvar x
  let vz: setvar z


  assert |- ( A e. CC -> ( CC _D ( CC X. { A } ) ) = ( CC X. { 0 } ) )

  proof
    cA
    cc
    wcel
    #
    vx
    vz
    cc0
    cc
    cA
    csn
    cxp
    #
    cc
    cA
    cc
    fconst6g
    @0
    vx
    cv
    #
    cc
    wcel
    #
    vz
    cv
    #
    cc
    wcel
    #
    @4
    @2
    wne
    #
    w3a
    #
    wa
    #
    @4
    @1
    cfv
    #
    @2
    @1
    cfv
    #
    cmin
    co
    #
    @4
    @2
    cmin
    co
    #
    cdiv
    co
    cc0
    @12
    cdiv
    co
    cc0
    @8
    @11
    cc0
    @12
    cdiv
    @8
    @11
    cA
    cA
    cmin
    co
    #
    cc0
    @8
    @9
    cA
    @10
    cA
    cmin
    @0
    @7
    @5
    @9
    cA
    wceq
    @0
    @3
    @5
    @6
    simpr2
    #
    cc
    cA
    @4
    cc
    fvconst2g
    syldan
    @0
    @5
    @3
    @10
    cA
    wceq
    @6
    cc
    cA
    @2
    cc
    fvconst2g
    3ad2antr1
    oveq12d
    @0
    @13
    cc0
    wceq
    @7
    cA
    subid
    adantr
    eqtrd
    oveq1d
    @8
    @12
    @8
    @4
    @2
    @14
    @0
    @3
    @5
    @6
    simpr1
    #
    subcld
    @8
    @4
    @2
    @14
    @15
    @0
    @3
    @5
    @6
    simpr3
    subne0d
    div0d
    eqtrd
    0cn
    dvidlem
end
