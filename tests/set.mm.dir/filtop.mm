include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cfbas.mm"
include "filfbas.mm"
include "fbasne0.mm"
include "syl.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "wss.mm"
include "filelss.mm"
include "wi.mm"
include "ssid.mm"
include "filss.mm"
include "3exp2.mm"
include "imp.mm"
include "mpi.mm"
include "mpd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"

theorem filtop
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( F e. ( Fil ` X ) -> X e. F )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cF
    c0
    wne
    #
    cX
    cF
    wcel
    #
    @0
    cF
    cX
    cfbas
    cfv
    wcel
    @1
    cF
    cX
    filfbas
    cX
    cF
    fbasne0
    syl
    @1
    vx
    cv
    #
    cF
    wcel
    #
    vx
    wex
    @0
    @2
    vx
    cF
    n0
    @0
    @4
    @2
    vx
    @0
    @4
    @2
    @0
    @4
    wa
    #
    @3
    cX
    wss
    #
    @2
    @3
    cF
    cX
    filelss
    @5
    cX
    cX
    wss
    #
    @6
    @2
    wi
    #
    cX
    ssid
    @0
    @4
    @7
    @8
    wi
    @0
    @4
    @7
    @6
    @2
    @3
    cX
    cF
    cX
    filss
    3exp2
    imp
    mpi
    mpd
    ex
    exlimdv
    syl5bi
    mpd
end
