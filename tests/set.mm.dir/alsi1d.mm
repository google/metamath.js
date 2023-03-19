include "wi.mm"
include "wal.mm"
include "wex.mm"
include "walsi.mm"
include "wa.mm"
include "df-alsi.mm"
include "sylib.mm"
include "simpld.mm"

theorem alsi1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vk: setvar k
  assume alsi1d.1: |- ( ph -> A! x ( ps -> ch ) )


  assert |- ( ph -> A. x ( ps -> ch ) )

  proof
    wph
    wps
    wch
    wi
    vx
    wal
    #
    wps
    vx
    wex
    #
    wph
    wps
    wch
    vx
    walsi
    @0
    @1
    wa
    alsi1d.1
    wps
    wch
    vx
    df-alsi
    sylib
    simpld
end
