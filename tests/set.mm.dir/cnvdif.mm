include "cdif.mm"
include "ccnv.mm"
include "relcnv.mm"
include "wss.mm"
include "wrel.mm"
include "difss.mm"
include "relss.mm"
include "mp2.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "vex.mm"
include "opelcnv.mm"
include "notbii.mm"
include "anbi12i.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem cnvdif
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- `' ( A \ B ) = ( `' A \ `' B )

  proof
    vx
    vy
    cA
    cB
    cdif
    #
    ccnv
    #
    cA
    ccnv
    #
    cB
    ccnv
    #
    cdif
    #
    @0
    relcnv
    @4
    @2
    wss
    @2
    wrel
    @4
    wrel
    @2
    @3
    difss
    cA
    relcnv
    @4
    @2
    relss
    mp2
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    @0
    wcel
    @7
    cA
    wcel
    #
    @7
    cB
    wcel
    #
    wn
    #
    wa
    #
    @6
    @5
    cop
    #
    @1
    wcel
    @12
    @4
    wcel
    #
    @7
    cA
    cB
    eldif
    @6
    @5
    @0
    vx
    vex
    #
    vy
    vex
    #
    opelcnv
    @13
    @12
    @2
    wcel
    #
    @12
    @3
    wcel
    #
    wn
    #
    wa
    @11
    @12
    @2
    @3
    eldif
    @16
    @8
    @18
    @10
    @6
    @5
    cA
    @14
    @15
    opelcnv
    @17
    @9
    @6
    @5
    cB
    @14
    @15
    opelcnv
    notbii
    anbi12i
    bitri
    3bitr4i
    eqrelriiv
end
