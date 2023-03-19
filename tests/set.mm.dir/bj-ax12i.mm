include "wal.mm"
include "wi.mm"
include "a1i.mm"
include "bj-ax12ig.mm"

theorem bj-ax12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-ax12i.1: |- ( ph -> ( ps <-> ch ) )
  assume bj-ax12i.2: |- ( ch -> A. x ch )


  assert |- ( ph -> ( ps -> A. x ( ph -> ps ) ) )

  proof
    wph
    wps
    wch
    vx
    bj-ax12i.1
    wch
    wch
    vx
    wal
    wi
    wph
    bj-ax12i.2
    a1i
    bj-ax12ig
end
