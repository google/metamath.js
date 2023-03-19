include "wi.mm"
include "wal.mm"
include "wa.mm"
include "pm5.32i.mm"
include "imp.mm"
include "biimprcd.mm"
include "sylg.mm"
include "sylbi.mm"
include "ex.mm"

theorem bj-ax12ig
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-ax12ig.1: |- ( ph -> ( ps <-> ch ) )
  assume bj-ax12ig.2: |- ( ph -> ( ch -> A. x ch ) )


  assert |- ( ph -> ( ps -> A. x ( ph -> ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wi
    #
    vx
    wal
    #
    wph
    wps
    wa
    wph
    wch
    wa
    #
    @1
    wph
    wps
    wch
    bj-ax12ig.1
    pm5.32i
    @2
    wch
    @0
    vx
    wph
    wch
    wch
    vx
    wal
    bj-ax12ig.2
    imp
    wph
    wps
    wch
    bj-ax12ig.1
    biimprcd
    sylg
    sylbi
    ex
end
