include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cinf.mm"
include "wne.mm"
include "cpred.mm"
include "csup.mm"
include "crab.mm"
include "cwlim.mm"
include "simpr.mm"
include "simpl.mm"
include "infeq123d.mm"
include "neeq2d.mm"
include "weq.mm"
include "equid.mm"
include "predeq123.mm"
include "mp3an3.mm"
include "supeq123d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-wlim.mm"
include "3eqtr4g.mm"

theorem wlimeq12
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vx: setvar x


  assert |- ( ( R = S /\ A = B ) -> WLim ( R , A ) = WLim ( S , B ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cB
    wceq
    #
    wa
    #
    vx
    cv
    #
    cA
    cA
    cR
    cinf
    #
    wne
    #
    @3
    cA
    cR
    @3
    cpred
    #
    cA
    cR
    csup
    #
    wceq
    #
    wa
    #
    vx
    cA
    crab
    @3
    cB
    cB
    cS
    cinf
    #
    wne
    #
    @3
    cB
    cS
    @3
    cpred
    #
    cB
    cS
    csup
    #
    wceq
    #
    wa
    #
    vx
    cB
    crab
    cA
    cR
    cwlim
    cB
    cS
    cwlim
    @2
    @9
    @15
    vx
    cA
    cB
    @0
    @1
    simpr
    #
    @2
    @5
    @11
    @8
    @14
    @2
    @4
    @10
    @3
    @2
    cA
    cA
    cR
    cB
    cB
    cS
    @16
    @16
    @0
    @1
    simpl
    #
    infeq123d
    neeq2d
    @2
    @7
    @13
    @3
    @2
    @6
    cA
    cR
    @12
    cB
    cS
    @0
    @1
    vx
    vx
    weq
    @6
    @12
    wceq
    vx
    equid
    cA
    cB
    cR
    cS
    @3
    @3
    predeq123
    mp3an3
    @16
    @17
    supeq123d
    eqeq2d
    anbi12d
    rabeqbidv
    vx
    cA
    cR
    df-wlim
    vx
    cB
    cS
    df-wlim
    3eqtr4g
end
