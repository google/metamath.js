include "csconn.mm"
include "cnlly.mm"
include "cconn.mm"
include "cii.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cpconn.mm"
include "sconnpconn.mm"
include "pconnconn.mm"
include "syl.mm"
include "ssriv.mm"
include "nllyss.mm"
include "ax-mp.mm"
include "clly.mm"
include "llyssnlly.mm"
include "iillysconn.mm"
include "sselii.mm"

theorem iinllyconn
  let vx: setvar x


  assert |- II e. N-Locally Conn

  proof
    csconn
    cnlly
    #
    cconn
    cnlly
    #
    cii
    csconn
    cconn
    wss
    @0
    @1
    wss
    vx
    csconn
    cconn
    vx
    cv
    #
    csconn
    wcel
    @2
    cpconn
    wcel
    @2
    cconn
    wcel
    @2
    sconnpconn
    @2
    pconnconn
    syl
    ssriv
    csconn
    cconn
    nllyss
    ax-mp
    csconn
    clly
    @0
    cii
    csconn
    llyssnlly
    iillysconn
    sselii
    sselii
end
