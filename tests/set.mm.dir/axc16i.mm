include "weq.mm"
include "wal.mm"
include "wi.mm"
include "nfv.mm"
include "ax7.mm"
include "cbv3.mm"
include "spimv.mm"
include "equcomi.mm"
include "syl.mm"
include "syl5com.mm"
include "alimdv.mm"
include "mpcom.mm"
include "alimi.mm"
include "biimpcd.mm"
include "nf5i.mm"
include "biimprd.mm"
include "syl6com.mm"
include "3syl.mm"

theorem axc16i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume axc16i.1: |- ( x = z -> ( ph <-> ps ) )
  assume axc16i.2: |- ( ps -> A. x ps )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( A. x x = y -> ( ph -> A. x ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    vz
    vy
    weq
    #
    vz
    wal
    #
    vx
    vz
    weq
    #
    vz
    wal
    #
    wph
    wph
    vx
    wal
    #
    wi
    @0
    @1
    vx
    vz
    @0
    vz
    nfv
    @1
    vx
    nfv
    vx
    vz
    vy
    ax7
    cbv3
    @2
    vz
    vx
    weq
    #
    vz
    wal
    #
    @4
    @0
    @2
    @7
    @1
    @0
    vz
    vx
    vz
    vx
    vy
    ax7
    spimv
    @0
    @1
    @6
    vz
    @0
    vy
    vx
    weq
    #
    @1
    @6
    vx
    vy
    equcomi
    @1
    vy
    vz
    weq
    @8
    @6
    wi
    vz
    vy
    equcomi
    vy
    vz
    vx
    ax7
    syl
    syl5com
    alimdv
    mpcom
    @6
    @3
    vz
    vz
    vx
    equcomi
    #
    alimi
    syl
    wph
    @4
    wps
    vz
    wal
    @5
    wph
    @3
    wps
    vz
    @3
    wph
    wps
    axc16i.1
    biimpcd
    alimdv
    wps
    wph
    vz
    vx
    wps
    vx
    axc16i.2
    nf5i
    wph
    vz
    nfv
    @6
    @3
    wps
    wph
    wi
    @9
    @3
    wph
    wps
    axc16i.1
    biimprd
    syl
    cbv3
    syl6com
    3syl
end
