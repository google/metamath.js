include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wcel.mm"
include "cc.mm"
include "crab.mm"
include "catan.mm"
include "cdm.mm"
include "wss.mm"
include "wi.mm"
include "rabss.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "simpl.mm"
include "logdmn0.mm"
include "adantl.mm"
include "atandm4.mm"
include "sylanbrc.mm"
include "ex.mm"
include "mprgbir.mm"
include "eqsstri.mm"

theorem atansssdm
  let vy: setvar y
  let cD: class D
  let cS: class S
  let cA: class A
  let vx: setvar x
  assume atansopn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume atansopn.s: |- S = { y e. CC | ( 1 + ( y ^ 2 ) ) e. D }

  disjoint D y
  disjoint A y
  disjoint x y
  disjoint D x
  disjoint S x
  assert |- S C_ dom arctan

  proof
    cS
    c1
    vy
    cv
    #
    c2
    cexp
    co
    caddc
    co
    #
    cD
    wcel
    #
    vy
    cc
    crab
    #
    catan
    cdm
    #
    atansopn.s
    @3
    @4
    wss
    @2
    @0
    @4
    wcel
    #
    wi
    vy
    cc
    @2
    vy
    cc
    @4
    rabss
    @0
    cc
    wcel
    #
    @2
    @5
    @6
    @2
    wa
    @6
    @1
    cc0
    wne
    #
    @5
    @6
    @2
    simpl
    @2
    @7
    @6
    @1
    cD
    atansopn.d
    logdmn0
    adantl
    @0
    atandm4
    sylanbrc
    ex
    mprgbir
    eqsstri
end
