include "weq.mm"
include "wi.mm"
include "wal.mm"
include "equtrr.mm"
include "ax12v.mm"
include "imim1d.mm"
include "alimdv.mm"
include "syl9r.mm"
include "syld.mm"
include "ax6evr.mm"
include "exlimiiv.mm"

theorem ax12v2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) )

  proof
    vy
    vz
    weq
    #
    vx
    vy
    weq
    #
    wph
    @1
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    vz
    @0
    @1
    vx
    vz
    weq
    #
    @4
    vy
    vz
    vx
    equtrr
    #
    @5
    wph
    @5
    wph
    wi
    #
    vx
    wal
    @0
    @3
    wph
    vx
    vz
    ax12v
    @0
    @7
    @2
    vx
    @0
    @1
    @5
    wph
    @6
    imim1d
    alimdv
    syl9r
    syld
    vz
    vy
    ax6evr
    exlimiiv
end
