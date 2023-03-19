include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "vprc.mm"
include "wa.mm"
include "vsnid.mm"
include "ax6ev.mm"
include "sneq.mm"
include "equcoms.mm"
include "eximii.mm"
include "snex.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "exbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mp2an.mm"
include "eluniab.mm"
include "mpbir.mm"
include "vex.mm"
include "2th.mm"
include "eqriv.mm"
include "eleq1i.mm"
include "mtbir.mm"
include "uniexg.mm"
include "mto.mm"
include "nelir.mm"

theorem snnexOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- { x | E. y x = { y } } e/ _V

  proof
    vx
    cv
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    wex
    #
    vx
    cab
    #
    cvv
    @5
    cvv
    wcel
    @5
    cuni
    #
    cvv
    wcel
    #
    @7
    cvv
    cvv
    wcel
    vprc
    @6
    cvv
    cvv
    vz
    @6
    cvv
    vz
    cv
    #
    @6
    wcel
    #
    @8
    cvv
    wcel
    @9
    @8
    @0
    wcel
    #
    @4
    wa
    #
    vx
    wex
    #
    @8
    @8
    csn
    #
    wcel
    #
    @13
    @2
    wceq
    #
    vy
    wex
    #
    @12
    vz
    vsnid
    @1
    @8
    wceq
    @15
    vy
    vy
    vz
    ax6ev
    @15
    vz
    vy
    @8
    @1
    sneq
    equcoms
    eximii
    @11
    @14
    @16
    wa
    vx
    @13
    @8
    snex
    @0
    @13
    wceq
    #
    @10
    @14
    @4
    @16
    @0
    @13
    @8
    eleq2
    @17
    @3
    @15
    vy
    @0
    @13
    @2
    eqeq1
    exbidv
    anbi12d
    spcev
    mp2an
    @4
    vx
    @8
    eluniab
    mpbir
    vz
    vex
    2th
    eqriv
    eleq1i
    mtbir
    @5
    cvv
    uniexg
    mto
    nelir
end
