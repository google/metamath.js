include "cv.mm"
include "cr.mm"
include "wss.mm"
include "c1.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "w3a.mm"
include "cn.mm"
include "wceq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "wb.mm"
include "dfnn2.mm"
include "eqeq2i.mm"
include "sylbir.mm"
include "nnssre.mm"
include "eqsstr3i.mm"
include "1nn.mm"
include "peano2nn.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "intabs.mm"
include "3anass.mm"
include "abbii.mm"
include "inteqi.mm"
include "3eqtr4ri.mm"

theorem dfnn3
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
  assert |- NN = |^| { x | ( x C_ RR /\ 1 e. x /\ A. y e. x ( y + 1 ) e. x ) }

  proof
    vx
    cv
    #
    cr
    wss
    #
    c1
    @0
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
    wa
    #
    vx
    cab
    #
    cint
    @7
    vx
    cab
    cint
    @1
    @2
    @6
    w3a
    #
    vx
    cab
    #
    cint
    cn
    @7
    c1
    vz
    cv
    #
    wcel
    #
    @4
    @12
    wcel
    #
    vy
    @12
    wral
    #
    wa
    #
    c1
    cn
    wcel
    #
    @4
    cn
    wcel
    #
    vy
    cn
    wral
    #
    wa
    #
    vx
    vz
    cr
    @0
    @12
    wceq
    @2
    @13
    @6
    @15
    @0
    @12
    c1
    eleq2
    @5
    @14
    vy
    @0
    @12
    @0
    @12
    @4
    eleq2
    raleqbi1dv
    anbi12d
    @0
    @16
    vz
    cab
    cint
    #
    wceq
    @0
    cn
    wceq
    #
    @7
    @20
    wb
    cn
    @21
    @0
    vz
    vy
    dfnn2
    #
    eqeq2i
    @22
    @2
    @17
    @6
    @19
    @0
    cn
    c1
    eleq2
    @5
    @18
    vy
    @0
    cn
    @0
    cn
    @4
    eleq2
    raleqbi1dv
    anbi12d
    sylbir
    @21
    cr
    wss
    @20
    @21
    cn
    cr
    @23
    nnssre
    eqsstr3i
    @17
    @19
    1nn
    @18
    vy
    cn
    @3
    peano2nn
    rgen
    pm3.2i
    pm3.2i
    intabs
    @11
    @9
    @10
    @8
    vx
    @1
    @2
    @6
    3anass
    abbii
    inteqi
    vx
    vy
    dfnn2
    3eqtr4ri
end
