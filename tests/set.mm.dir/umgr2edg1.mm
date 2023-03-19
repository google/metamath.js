include "cumgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "wn.mm"
include "w3a.mm"
include "umgr2edg.mm"
include "3anrot.mm"
include "df-ne.mm"
include "3anbi3i.mm"
include "bitri.mm"
include "df-3an.mm"
include "2rexbii.mm"
include "sylib.mm"
include "rexanali.mm"
include "rexbii.mm"
include "rexnal.mm"
include "intnand.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "reu4.mm"
include "sylnibr.mm"

theorem umgr2edg1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  let vy: setvar y
  assume usgrf1oedg.i: |- I = ( iEdg ` G )
  assume usgrf1oedg.e: |- E = ( Edg ` G )

  disjoint G x
  disjoint A x
  disjoint B x
  disjoint I x
  disjoint N x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint G y
  disjoint I y
  disjoint N y
  assert |- ( ( ( G e. UMGraph /\ A =/= B ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> -. E! x e. dom I N e. ( I ` x ) )

  proof
    cG
    cumgr
    wcel
    cA
    cB
    wne
    wa
    cN
    cA
    cpr
    cE
    wcel
    cB
    cN
    cpr
    cE
    wcel
    wa
    wa
    #
    cN
    vx
    cv
    #
    cI
    cfv
    #
    wcel
    #
    vx
    cI
    cdm
    #
    wrex
    #
    @3
    cN
    vy
    cv
    #
    cI
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    vy
    @4
    wral
    #
    vx
    @4
    wral
    #
    wa
    @3
    vx
    @4
    wreu
    @0
    @12
    @5
    @0
    @9
    @10
    wn
    #
    wa
    #
    vy
    @4
    wrex
    #
    vx
    @4
    wrex
    #
    @12
    wn
    #
    @0
    @1
    @6
    wne
    #
    @3
    @8
    w3a
    #
    vy
    @4
    wrex
    vx
    @4
    wrex
    @16
    vx
    vy
    cA
    cB
    cE
    cG
    cI
    cN
    usgrf1oedg.i
    usgrf1oedg.e
    umgr2edg
    @19
    @14
    vx
    vy
    @4
    @4
    @19
    @3
    @8
    @13
    w3a
    #
    @14
    @19
    @3
    @8
    @18
    w3a
    @20
    @18
    @3
    @8
    3anrot
    @18
    @13
    @3
    @8
    @1
    @6
    df-ne
    3anbi3i
    bitri
    @3
    @8
    @13
    df-3an
    bitri
    2rexbii
    sylib
    @16
    @11
    wn
    #
    vx
    @4
    wrex
    @17
    @15
    @21
    vx
    @4
    @9
    @10
    vy
    @4
    rexanali
    rexbii
    @11
    vx
    @4
    rexnal
    bitri
    sylib
    intnand
    @3
    @8
    vx
    vy
    @4
    @10
    @2
    @7
    cN
    @1
    @6
    cI
    fveq2
    eleq2d
    reu4
    sylnibr
end
