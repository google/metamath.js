include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "wi.mm"
include "ax6ev.mm"
include "dveeq2.mm"
include "ax12v.mm"
include "wb.mm"
include "equequ2.mm"
include "sps.mm"
include "nfa1.mm"
include "imbi1d.mm"
include "albid.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "syl6.mm"
include "exlimdv.mm"
include "mpi.mm"

theorem axc15
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    vz
    vy
    weq
    #
    vz
    wex
    @0
    wph
    @0
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    vz
    vy
    ax6ev
    @1
    @2
    @6
    vz
    @1
    @2
    @2
    vx
    wal
    #
    @6
    vx
    vy
    vz
    dveeq2
    @7
    vx
    vz
    weq
    #
    wph
    @8
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    @6
    wph
    vx
    vz
    ax12v
    @7
    @8
    @0
    @11
    @5
    @2
    @8
    @0
    wb
    vx
    vz
    vy
    vx
    equequ2
    sps
    #
    @7
    @10
    @4
    wph
    @7
    @9
    @3
    vx
    @2
    vx
    nfa1
    @7
    @8
    @0
    wph
    @12
    imbi1d
    albid
    imbi2d
    imbi12d
    mpbii
    syl6
    exlimdv
    mpi
end
