include "cvol.mm"
include "cdm.mm"
include "cr.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "elex.mm"
include "mblss.mm"
include "elpwd.mm"
include "rgen.mm"
include "dfss3.mm"
include "mpbir.mm"

theorem dmvolss
  let vk: setvar k
  let vx: setvar x


  assert |- dom vol C_ ~P RR

  proof
    cvol
    cdm
    #
    cr
    cpw
    #
    wss
    vx
    cv
    #
    @1
    wcel
    #
    vx
    @0
    wral
    @3
    vx
    @0
    @2
    @0
    wcel
    @2
    cr
    cvv
    @2
    @0
    elex
    @2
    mblss
    elpwd
    rgen
    vx
    @0
    @1
    dfss3
    mpbir
end
