include "cumgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cuhgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cdm.mm"
include "wrex.mm"
include "umgruhgr.mm"
include "anim1i.mm"
include "adantr.mm"
include "eqid.mm"
include "umgrpredgv.mm"
include "ad2ant2r.mm"
include "simprd.mm"
include "ad2ant2rl.mm"
include "simpld.mm"
include "3jca.mm"
include "simpr.mm"
include "uhgr2edg.mm"
include "syl.mm"

theorem umgr2edg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  assume usgrf1oedg.i: |- I = ( iEdg ` G )
  assume usgrf1oedg.e: |- E = ( Edg ` G )

  disjoint G x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint N x
  disjoint N y
  assert |- ( ( ( G e. UMGraph /\ A =/= B ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> E. x e. dom I E. y e. dom I ( x =/= y /\ N e. ( I ` x ) /\ N e. ( I ` y ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    cN
    cA
    cpr
    cE
    wcel
    #
    cB
    cN
    cpr
    cE
    wcel
    #
    wa
    #
    wa
    #
    cG
    cuhgr
    wcel
    #
    @1
    wa
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cB
    @9
    wcel
    #
    cN
    @9
    wcel
    #
    w3a
    #
    @5
    w3a
    vx
    cv
    #
    vy
    cv
    #
    wne
    cN
    @14
    cI
    cfv
    wcel
    cN
    @15
    cI
    cfv
    wcel
    w3a
    vy
    cI
    cdm
    #
    wrex
    vx
    @16
    wrex
    @6
    @8
    @13
    @5
    @2
    @8
    @5
    @0
    @7
    @1
    cG
    umgruhgr
    anim1i
    adantr
    @6
    @10
    @11
    @12
    @6
    @12
    @10
    @0
    @3
    @12
    @10
    wa
    @1
    @4
    cE
    cG
    cN
    cA
    @9
    @9
    eqid
    #
    usgrf1oedg.e
    umgrpredgv
    ad2ant2r
    #
    simprd
    @6
    @11
    @12
    @0
    @4
    @11
    @12
    wa
    @1
    @3
    cE
    cG
    cB
    cN
    @9
    @17
    usgrf1oedg.e
    umgrpredgv
    ad2ant2rl
    simpld
    @6
    @12
    @10
    @18
    simpld
    3jca
    @2
    @5
    simpr
    3jca
    vx
    vy
    cA
    cB
    cE
    cG
    cI
    cN
    @9
    usgrf1oedg.i
    usgrf1oedg.e
    @17
    uhgr2edg
    syl
end
