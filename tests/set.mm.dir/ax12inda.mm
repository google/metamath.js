include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wex.mm"
include "ax6ev.mm"
include "wa.mm"
include "ax12inda2.mm"
include "wb.mm"
include "dveeq2-o.mm"
include "imp.mm"
include "hba1-o.mm"
include "equequ2.mm"
include "sps-o.mm"
include "albidh.mm"
include "notbid.mm"
include "syl.mm"
include "adantl.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpi.mm"
include "pm2.43i.mm"

theorem ax12inda
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume ax12inda.1: |- ( -. A. x x = w -> ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) )

  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wn
    #
    @0
    wph
    vz
    wal
    #
    @0
    @3
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    @2
    vw
    vy
    weq
    #
    vw
    wex
    @2
    @7
    wi
    #
    vw
    vy
    ax6ev
    @2
    @8
    @9
    vw
    @2
    @8
    @9
    @2
    @8
    wa
    #
    vx
    vw
    weq
    #
    vx
    wal
    #
    wn
    #
    @11
    @3
    @11
    @3
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    wi
    @9
    wph
    vx
    vw
    vz
    ax12inda.1
    ax12inda2
    @10
    @13
    @2
    @17
    @7
    @10
    @8
    vx
    wal
    #
    @13
    @2
    wb
    @2
    @8
    @18
    vx
    vy
    vw
    dveeq2-o
    imp
    #
    @18
    @12
    @1
    @18
    @11
    @0
    vx
    @8
    vx
    hba1-o
    #
    @8
    @11
    @0
    wb
    #
    vx
    vw
    vy
    vx
    equequ2
    #
    sps-o
    #
    albidh
    notbid
    syl
    @10
    @11
    @0
    @16
    @6
    @8
    @21
    @2
    @22
    adantl
    @10
    @15
    @5
    @3
    @10
    @18
    @15
    @5
    wb
    @19
    @18
    @14
    @4
    vx
    @20
    @18
    @11
    @0
    @3
    @23
    imbi1d
    albidh
    syl
    imbi2d
    imbi12d
    imbi12d
    mpbii
    ex
    exlimdv
    mpi
    pm2.43i
end
