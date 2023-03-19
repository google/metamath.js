include "wrel.mm"
include "wer.mm"
include "ccnv.mm"
include "wceq.mm"
include "errel.mm"
include "relcnv.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "id.mm"
include "ersymb.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "bitr3i.mm"
include "3bitr3g.mm"
include "eqrelrdv2.mm"
include "mpanl1.mm"
include "mpancom.mm"

theorem ercnv
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R Er A -> `' R = R )

  proof
    cR
    wrel
    #
    cA
    cR
    wer
    #
    cR
    ccnv
    #
    cR
    wceq
    #
    cA
    cR
    errel
    @2
    wrel
    @0
    @1
    @3
    cR
    relcnv
    @1
    vx
    vy
    @2
    cR
    @1
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    @5
    @4
    cR
    wbr
    @5
    @4
    cop
    #
    @2
    wcel
    #
    @7
    cR
    wcel
    @1
    @4
    @5
    cR
    cA
    @1
    id
    ersymb
    @6
    @5
    @4
    @2
    wbr
    @8
    @5
    @4
    cR
    vx
    vex
    vy
    vex
    brcnv
    @5
    @4
    @2
    df-br
    bitr3i
    @5
    @4
    cR
    df-br
    3bitr3g
    eqrelrdv2
    mpanl1
    mpancom
end
