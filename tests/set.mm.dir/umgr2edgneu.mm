include "cumgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "wn.mm"
include "w3a.mm"
include "umgrvad2edg.mm"
include "3simpc.mm"
include "neneq.mm"
include "3ad2ant1.mm"
include "jca.mm"
include "reximi.mm"
include "syl.mm"
include "rexanali.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylib.mm"
include "intnand.mm"
include "eleq2.mm"
include "reu4.mm"
include "sylnibr.mm"

theorem umgr2edgneu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cN: class N
  let vy: setvar y
  assume umgrvad2edg.e: |- E = ( Edg ` G )

  disjoint A x
  disjoint B x
  disjoint E x
  disjoint G x
  disjoint N x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint E y
  disjoint G y
  disjoint N y
  assert |- ( ( ( G e. UMGraph /\ A =/= B ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> -. E! x e. E N e. x )

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
    wcel
    #
    vx
    cE
    wrex
    #
    @2
    cN
    vy
    cv
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
    cE
    wral
    #
    vx
    cE
    wral
    #
    wa
    @2
    vx
    cE
    wreu
    @0
    @9
    @3
    @0
    @6
    @7
    wn
    #
    wa
    #
    vy
    cE
    wrex
    #
    vx
    cE
    wrex
    #
    @9
    wn
    #
    @0
    @1
    @4
    wne
    #
    @2
    @5
    w3a
    #
    vy
    cE
    wrex
    #
    vx
    cE
    wrex
    @13
    vx
    vy
    cA
    cB
    cE
    cG
    cN
    umgrvad2edg.e
    umgrvad2edg
    @17
    @12
    vx
    cE
    @16
    @11
    vy
    cE
    @16
    @6
    @10
    @15
    @2
    @5
    3simpc
    @15
    @2
    @10
    @5
    @1
    @4
    neneq
    3ad2ant1
    jca
    reximi
    reximi
    syl
    @13
    @8
    wn
    #
    vx
    cE
    wrex
    @14
    @12
    @18
    vx
    cE
    @6
    @7
    vy
    cE
    rexanali
    rexbii
    @8
    vx
    cE
    rexnal
    bitri
    sylib
    intnand
    @2
    @5
    vx
    vy
    cE
    @1
    @4
    cN
    eleq2
    reu4
    sylnibr
end
