include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "csetrecs.mm"
include "fveq1.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "albidv.mm"
include "imbi1d.mm"
include "abbidv.mm"
include "unieqd.mm"
include "df-setrecs.mm"
include "3eqtr4g.mm"

theorem setrecseq
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- ( F = G -> setrecs ( F ) = setrecs ( G ) )

  proof
    cF
    cG
    wceq
    #
    vw
    cv
    #
    vy
    cv
    #
    wss
    #
    @1
    vz
    cv
    #
    wss
    #
    @1
    cF
    cfv
    #
    @4
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @2
    @4
    wss
    #
    wi
    #
    vz
    wal
    #
    vy
    cab
    #
    cuni
    @3
    @5
    @1
    cG
    cfv
    #
    @4
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @11
    wi
    #
    vz
    wal
    #
    vy
    cab
    #
    cuni
    cF
    csetrecs
    cG
    csetrecs
    @0
    @14
    @22
    @0
    @13
    @21
    vy
    @0
    @12
    @20
    vz
    @0
    @10
    @19
    @11
    @0
    @9
    @18
    vw
    @0
    @8
    @17
    @3
    @0
    @7
    @16
    @5
    @0
    @6
    @15
    @4
    @1
    cF
    cG
    fveq1
    sseq1d
    imbi2d
    imbi2d
    albidv
    imbi1d
    albidv
    abbidv
    unieqd
    vy
    vz
    vw
    cF
    df-setrecs
    vy
    vz
    vw
    cG
    df-setrecs
    3eqtr4g
end
