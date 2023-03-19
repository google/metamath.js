include "orcomd.mm"
include "unitresl.mm"

theorem unitresr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume unitresr.1: |- ( ph -> ( ps \/ ch ) )
  assume unitresr.2: |- ( ph -> -. ps )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    unitresr.1
    orcomd
    unitresr.2
    unitresl
end
