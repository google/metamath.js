include "id.mm"
include "orim12i.mm"

theorem orim1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orim1i.1: |- ( ph -> ps )


  assert |- ( ( ph \/ ch ) -> ( ps \/ ch ) )

  proof
    wph
    wps
    wch
    wch
    orim1i.1
    wch
    id
    orim12i
end
