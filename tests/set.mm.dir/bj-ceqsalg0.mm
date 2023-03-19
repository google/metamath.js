include "wnf.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "ax-gen.mm"
include "bj-ceqsalt0.mm"
include "mp3an12.mm"

theorem bj-ceqsalg0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-ceqsalg0.1: |- F/ x ps
  assume bj-ceqsalg0.2: |- ( ch -> ( ph <-> ps ) )


  assert |- ( E. x ch -> ( A. x ( ch -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    wch
    wph
    wps
    wb
    wi
    #
    vx
    wal
    wch
    vx
    wex
    wch
    wph
    wi
    vx
    wal
    wps
    wb
    bj-ceqsalg0.1
    @0
    vx
    bj-ceqsalg0.2
    ax-gen
    wph
    wps
    wch
    vx
    bj-ceqsalt0
    mp3an12
end
