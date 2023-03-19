include "weq.mm"
include "wi.mm"
include "wal.mm"
include "biimpd.mm"
include "bj-equsal1.mm"
include "biimprd.mm"
include "bj-equsal2.mm"
include "impbii.mm"

theorem bj-equsal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-equsal.1: |- F/ x ps
  assume bj-equsal.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x ( x = y -> ph ) <-> ps )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    wps
    wph
    wps
    vx
    vy
    bj-equsal.1
    @0
    wph
    wps
    bj-equsal.2
    biimpd
    bj-equsal1
    wps
    wph
    vx
    vy
    bj-equsal.1
    @0
    wph
    wps
    bj-equsal.2
    biimprd
    bj-equsal2
    impbii
end
