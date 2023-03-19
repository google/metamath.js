include "ax-3.mm"

theorem con4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )

  proof
    wph
    wps
    ax-3
end
