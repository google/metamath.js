include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wss.mm"
include "wi.mm"
include "ssintab.mm"
include "peano5uzi.mm"
include "mpgbir.mm"
include "zrei.mm"
include "leidi.mm"
include "breq2.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "peano2uz2.mm"
include "mpan.mm"
include "rgen.mm"
include "zex.mm"
include "rabex.mm"
include "wceq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elab.mm"
include "intss1.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem dfuzi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  assume dfuzi.1: |- N e. ZZ

  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  assert |- { z e. ZZ | N <_ z } = |^| { x | ( N e. x /\ A. y e. x ( y + 1 ) e. x ) }

  proof
    cN
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cz
    crab
    #
    cN
    vx
    cv
    #
    wcel
    #
    vy
    cv
    #
    c1
    caddc
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    @2
    @11
    wss
    @9
    @2
    @3
    wss
    wi
    vx
    @9
    vx
    @2
    ssintab
    vy
    @3
    vz
    cN
    dfuzi.1
    peano5uzi
    mpgbir
    @2
    @10
    wcel
    #
    @11
    @2
    wss
    @12
    cN
    @2
    wcel
    #
    @6
    @2
    wcel
    #
    vy
    @2
    wral
    #
    @13
    cN
    cz
    wcel
    #
    cN
    cN
    cle
    wbr
    #
    dfuzi.1
    cN
    cN
    dfuzi.1
    zrei
    leidi
    @1
    @17
    vz
    cN
    cz
    @0
    cN
    cN
    cle
    breq2
    elrab
    mpbir2an
    @14
    vy
    @2
    @16
    @5
    @2
    wcel
    @14
    dfuzi.1
    vz
    cN
    @5
    peano2uz2
    mpan
    rgen
    @9
    @13
    @15
    wa
    vx
    @2
    @1
    vz
    cz
    zex
    rabex
    @3
    @2
    wceq
    @4
    @13
    @8
    @15
    @3
    @2
    cN
    eleq2
    @7
    @14
    vy
    @3
    @2
    @3
    @2
    @6
    eleq2
    raleqbi1dv
    anbi12d
    elab
    mpbir2an
    @2
    @10
    intss1
    ax-mp
    eqssi
end
