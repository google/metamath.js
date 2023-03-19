include "c0.mm"
include "ccf.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "ccrd.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cfub.mm"
include "csn.mm"
include "0ss.mm"
include "biantru.mm"
include "ss0b.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "0ex.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "card0.mm"
include "eqeq2i.mm"
include "abbii.mm"
include "df-sn.mm"
include "eqtr4i.mm"
include "inteqi.mm"
include "intsn.mm"
include "eqtri.mm"
include "sseqtri.mm"
include "mpbi.mm"

theorem cf0
  let vx: setvar x
  let vy: setvar y


  assert |- ( cf ` (/) ) = (/)

  proof
    c0
    ccf
    cfv
    #
    c0
    wss
    @0
    c0
    wceq
    @0
    vx
    cv
    #
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @2
    c0
    wss
    #
    c0
    @2
    cuni
    #
    wss
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    c0
    vx
    vy
    c0
    cfub
    @12
    c0
    csn
    #
    cint
    c0
    @11
    @13
    @11
    @1
    c0
    wceq
    #
    vx
    cab
    @13
    @10
    @14
    vx
    @10
    @2
    c0
    wceq
    #
    @4
    wa
    #
    vy
    wex
    #
    @14
    @9
    @16
    vy
    @9
    @4
    @15
    wa
    @16
    @8
    @15
    @4
    @8
    @5
    @15
    @7
    @5
    @6
    0ss
    biantru
    @2
    ss0b
    bitr3i
    anbi2i
    @4
    @15
    ancom
    bitri
    exbii
    @17
    @1
    c0
    ccrd
    cfv
    #
    wceq
    #
    @14
    @4
    @19
    vy
    c0
    0ex
    @15
    @3
    @18
    @1
    @2
    c0
    ccrd
    fveq2
    eqeq2d
    ceqsexv
    @18
    c0
    @1
    card0
    eqeq2i
    bitri
    bitri
    abbii
    vx
    c0
    df-sn
    eqtr4i
    inteqi
    c0
    0ex
    intsn
    eqtri
    sseqtri
    @0
    ss0b
    mpbi
end
