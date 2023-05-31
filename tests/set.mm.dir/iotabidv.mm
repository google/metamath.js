include "wb.mm"
include "wal.mm"
include "cio.mm"
include "wceq.mm"
include "alrimiv.mm"
include "iotabi.mm"
include "syl.mm"

theorem iotabidv
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume iotabidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( iota x ps ) = ( iota x ch ) )

  proof
    wph
    wps
    wch
    wb
    #
    vx
    wal
    wps
    vx
    cio
    wch
    vx
    cio
    wceq
    wph
    @0
    vx
    iotabidv.1
    alrimiv
    wps
    wch
    vx
    iotabi
    syl
end
