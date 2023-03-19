include "wn.mm"
include "id.mm"
include "nsyl2.mm"

theorem con1i
  let wph: wff ph
  let wps: wff ps
  assume con1i.1: |- ( -. ph -> ps )


  assert |- ( -. ps -> ph )

  proof
    wps
    wn
    #
    wps
    wph
    @0
    id
    con1i.1
    nsyl2
end
