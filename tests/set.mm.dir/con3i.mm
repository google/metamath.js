include "wn.mm"
include "id.mm"
include "nsyl.mm"

theorem con3i
  let wph: wff ph
  let wps: wff ps
  assume con3i.a: |- ( ph -> ps )


  assert |- ( -. ps -> -. ph )

  proof
    wps
    wn
    #
    wps
    wph
    @0
    id
    con3i.a
    nsyl
end
