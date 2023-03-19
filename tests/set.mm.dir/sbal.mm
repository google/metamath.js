include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wb.mm"
include "nfae.mm"
include "axc16gb.mm"
include "sbbid.mm"
include "bitr3d.mm"
include "sbal1.mm"
include "pm2.61i.mm"

theorem sbal
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph )

  proof
    vx
    vz
    weq
    vx
    wal
    #
    wph
    vx
    wal
    #
    vy
    vz
    wsb
    #
    wph
    vy
    vz
    wsb
    #
    vx
    wal
    #
    wb
    @0
    @3
    @2
    @4
    @0
    wph
    @1
    vy
    vz
    vx
    vz
    vy
    nfae
    wph
    vx
    vz
    vx
    axc16gb
    sbbid
    @3
    vx
    vz
    vx
    axc16gb
    bitr3d
    wph
    vx
    vy
    vz
    sbal1
    pm2.61i
end
