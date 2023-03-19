include "id.mm"
include "nsyl3.mm"

theorem con2i
  let wph: wff ph
  let wps: wff ps
  assume con2i.a: |- ( ph -> -. ps )


  assert |- ( ps -> -. ph )

  proof
    wph
    wps
    wps
    con2i.a
    wps
    id
    nsyl3
end
