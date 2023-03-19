include "cn.mm"
include "c1.mm"
include "cv.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wss.mm"
include "wi.mm"
include "1ex.mm"
include "elintab.mm"
include "simpl.mm"
include "mpgbir.mm"
include "wal.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "adantl.mm"
include "a2i.mm"
include "alimi.mm"
include "vex.mm"
include "ovex.mm"
include "3imtr4i.mm"
include "rgen.mm"
include "peano5nni.mm"
include "mp2an.mm"
include "1nn.mm"
include "peano2nn.mm"
include "nnex.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elab.mm"
include "mpbir2an.mm"
include "intss1.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem dfnn2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- NN = |^| { x | ( 1 e. x /\ A. y e. x ( y + 1 ) e. x ) }

  proof
    cn
    c1
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
    @0
    wcel
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    c1
    @8
    wcel
    #
    vz
    cv
    #
    c1
    caddc
    co
    #
    @8
    wcel
    #
    vz
    @8
    wral
    cn
    @8
    wss
    @9
    @6
    @1
    wi
    vx
    @6
    vx
    c1
    1ex
    elintab
    @1
    @5
    simpl
    mpgbir
    @12
    vz
    @8
    @6
    @10
    @0
    wcel
    #
    wi
    #
    vx
    wal
    @6
    @11
    @0
    wcel
    #
    wi
    #
    vx
    wal
    @10
    @8
    wcel
    @12
    @14
    @16
    vx
    @6
    @13
    @15
    @5
    @13
    @15
    wi
    @1
    @4
    @15
    vy
    @10
    @0
    @2
    @10
    wceq
    @3
    @11
    @0
    @2
    @10
    c1
    caddc
    oveq1
    eleq1d
    rspccv
    adantl
    a2i
    alimi
    @6
    vx
    @10
    vz
    vex
    elintab
    @6
    vx
    @11
    @10
    c1
    caddc
    ovex
    elintab
    3imtr4i
    rgen
    vz
    @8
    peano5nni
    mp2an
    cn
    @7
    wcel
    #
    @8
    cn
    wss
    @17
    c1
    cn
    wcel
    #
    @3
    cn
    wcel
    #
    vy
    cn
    wral
    #
    1nn
    @19
    vy
    cn
    @2
    peano2nn
    rgen
    @6
    @18
    @20
    wa
    vx
    cn
    nnex
    @0
    cn
    wceq
    @1
    @18
    @5
    @20
    @0
    cn
    c1
    eleq2
    @4
    @19
    vy
    @0
    cn
    @0
    cn
    @3
    eleq2
    raleqbi1dv
    anbi12d
    elab
    mpbir2an
    cn
    @7
    intss1
    ax-mp
    eqssi
end
