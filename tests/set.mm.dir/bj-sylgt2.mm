include "wi.mm"
include "wal.mm"
include "sylgt.mm"
include "imp.mm"

theorem bj-sylgt2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( A. x ( ps -> ch ) /\ ( ph -> A. x ps ) ) -> ( ph -> A. x ch ) )

  proof
    wps
    wch
    wi
    vx
    wal
    wph
    wps
    vx
    wal
    wi
    wph
    wch
    vx
    wal
    wi
    wph
    wps
    wch
    vx
    sylgt
    imp
end
