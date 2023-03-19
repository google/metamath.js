include "wal.mm"
include "weq.mm"
include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "syl6.mm"
include "cbv1h.mm"
include "equcomi.mm"
include "biimpr.mm"
include "syl56.mm"
include "alcoms.mm"
include "impbid.mm"

theorem cbv2h
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbv2h.1: |- ( ph -> ( ps -> A. y ps ) )
  assume cbv2h.2: |- ( ph -> ( ch -> A. x ch ) )
  assume cbv2h.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )


  assert |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    vy
    wal
    vx
    wal
    wps
    vx
    wal
    #
    wch
    vy
    wal
    #
    wph
    wps
    wch
    vx
    vy
    cbv2h.1
    cbv2h.2
    wph
    vx
    vy
    weq
    #
    wps
    wch
    wb
    #
    wps
    wch
    wi
    cbv2h.3
    wps
    wch
    biimp
    syl6
    cbv1h
    wph
    @1
    @0
    wi
    vy
    vx
    wph
    wch
    wps
    vy
    vx
    cbv2h.2
    cbv2h.1
    vy
    vx
    weq
    @2
    wph
    @3
    wch
    wps
    wi
    vy
    vx
    equcomi
    cbv2h.3
    wps
    wch
    biimpr
    syl56
    cbv1h
    alcoms
    impbid
end
