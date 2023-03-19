include "nf5i.mm"
include "exlimd.mm"

theorem exlimdh
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimdh.1: |- ( ph -> A. x ph )
  assume exlimdh.2: |- ( ch -> A. x ch )
  assume exlimdh.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( E. x ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    exlimdh.1
    nf5i
    wch
    vx
    exlimdh.2
    nf5i
    exlimdh.3
    exlimd
end
