include "cun.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "df-cnv.mm"
include "wo.mm"
include "unopab.mm"
include "brun.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "uneq12i.mm"

theorem cnvun
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- `' ( A u. B ) = ( `' A u. `' B )

  proof
    cA
    cB
    cun
    #
    ccnv
    #
    vy
    cv
    #
    vx
    cv
    #
    cA
    wbr
    #
    vx
    vy
    copab
    #
    @2
    @3
    cB
    wbr
    #
    vx
    vy
    copab
    #
    cun
    #
    cA
    ccnv
    #
    cB
    ccnv
    #
    cun
    @1
    @2
    @3
    @0
    wbr
    #
    vx
    vy
    copab
    #
    @8
    vx
    vy
    @0
    df-cnv
    @8
    @4
    @6
    wo
    #
    vx
    vy
    copab
    @12
    @4
    @6
    vx
    vy
    unopab
    @11
    @13
    vx
    vy
    @2
    @3
    cA
    cB
    brun
    opabbii
    eqtr4i
    eqtr4i
    @9
    @5
    @10
    @7
    vx
    vy
    cA
    df-cnv
    vx
    vy
    cB
    df-cnv
    uneq12i
    eqtr4i
end
