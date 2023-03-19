include "wi.mm"
include "imim2d.mm"
include "mpid.mm"

theorem embantd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume embantd.1: |- ( ph -> ps )
  assume embantd.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ( ps -> ch ) -> th ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wth
    embantd.1
    wph
    wch
    wth
    wps
    embantd.2
    imim2d
    mpid
end
