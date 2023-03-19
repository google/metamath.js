include "wal.mm"
include "weq.mm"
include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "syl6.mm"
include "bj-cbv1hv.mm"
include "equcomi.mm"
include "biimpr.mm"
include "syl56.mm"
include "alcoms.mm"
include "impbid.mm"

theorem bj-cbv2hv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbv2hv.1: |- ( ph -> ( ps -> A. y ps ) )
  assume bj-cbv2hv.2: |- ( ph -> ( ch -> A. x ch ) )
  assume bj-cbv2hv.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )

  disjoint x y
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
    bj-cbv2hv.1
    bj-cbv2hv.2
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
    bj-cbv2hv.3
    wps
    wch
    biimp
    syl6
    bj-cbv1hv
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
    bj-cbv2hv.2
    bj-cbv2hv.1
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
    bj-cbv2hv.3
    wps
    wch
    biimpr
    syl56
    bj-cbv1hv
    alcoms
    impbid
end
