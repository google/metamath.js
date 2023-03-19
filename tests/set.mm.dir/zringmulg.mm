include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "ccnfld.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "zring.mm"
include "cmul.mm"
include "csubg.mm"
include "wceq.mm"
include "c1.mm"
include "cv.mm"
include "zcn.mm"
include "zaddcl.mm"
include "znegcl.mm"
include "1z.mm"
include "cnsubglem.mm"
include "eqid.mm"
include "df-zring.mm"
include "subgmulg.mm"
include "mp3an1.mm"
include "cc.mm"
include "simpr.mm"
include "zcnd.mm"
include "cnfldmulg.mm"
include "syldan.mm"
include "eqtr3d.mm"

theorem zringmulg
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A ( .g ` ZZring ) B ) = ( A x. B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    ccnfld
    cmg
    cfv
    #
    co
    #
    cA
    cB
    zring
    cmg
    cfv
    #
    co
    #
    cA
    cB
    cmul
    co
    #
    cz
    ccnfld
    csubg
    cfv
    wcel
    @0
    @1
    @4
    @6
    wceq
    vx
    vy
    cz
    c1
    vx
    cv
    #
    zcn
    @8
    vy
    cv
    zaddcl
    @8
    znegcl
    1z
    cnsubglem
    cz
    @5
    @3
    ccnfld
    zring
    cA
    cB
    @3
    eqid
    df-zring
    @5
    eqid
    subgmulg
    mp3an1
    @0
    @1
    cB
    cc
    wcel
    @4
    @7
    wceq
    @2
    cB
    @0
    @1
    simpr
    zcnd
    cA
    cB
    cnfldmulg
    syldan
    eqtr3d
end
