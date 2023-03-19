include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "wi.mm"
include "ax6ev.mm"
include "wa.mm"
include "wb.mm"
include "equequ2.mm"
include "adantl.mm"
include "dveeq2-o.mm"
include "imp.mm"
include "nfa1-o.mm"
include "imbi1d.mm"
include "sps-o.mm"
include "albid.mm"
include "syl.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpi.mm"

theorem ax12v2-o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax12v2-o.1: |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) )

  disjoint x z
  disjoint y z
  disjoint ph z
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
    @6
    @1
    @2
    wa
    #
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
    ax12v2-o.1
    @7
    @8
    @0
    @11
    @5
    @2
    @8
    @0
    wb
    @1
    vz
    vy
    vx
    equequ2
    #
    adantl
    @7
    @10
    @4
    wph
    @7
    @2
    vx
    wal
    #
    @10
    @4
    wb
    @1
    @2
    @13
    vx
    vy
    vz
    dveeq2-o
    imp
    @13
    @9
    @3
    vx
    @2
    vx
    nfa1-o
    @2
    @9
    @3
    wb
    vx
    @2
    @8
    @0
    wph
    @12
    imbi1d
    sps-o
    albid
    syl
    imbi2d
    imbi12d
    mpbii
    ex
    exlimdv
    mpi
end
