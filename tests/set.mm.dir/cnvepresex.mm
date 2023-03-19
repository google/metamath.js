include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cv.mm"
include "wa.mm"
include "copab.mm"
include "cvv.mm"
include "cnvepres.mm"
include "elex.mm"
include "cab.mm"
include "abid2.mm"
include "vex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "opabex3d.mm"
include "syl5eqel.mm"

theorem cnvepresex
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( `' _E |` A ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cep
    ccnv
    cA
    cres
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    @1
    wcel
    #
    wa
    vx
    vy
    copab
    cvv
    vx
    vy
    cA
    cnvepres
    @0
    @3
    vx
    vy
    cA
    cA
    cV
    elex
    @3
    vy
    cab
    #
    cvv
    wcel
    @0
    @2
    wa
    @4
    @1
    cvv
    vy
    @1
    abid2
    vx
    vex
    eqeltri
    a1i
    opabex3d
    syl5eqel
end
