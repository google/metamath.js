include "ax-3.mm"

theorem con4
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )

  proof
    wph
    wps
    ax-3
end
