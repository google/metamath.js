include "wn.mm"
include "notnot.mm"
include "nsyl2.mm"

theorem con4iOLD
  let wph: wff ph
  let wps: wff ps
  assume con4iOLD.1: |- ( -. ph -> -. ps )


  assert |- ( ps -> ph )

  proof
    wps
    wps
    wn
    wph
    wps
    notnot
    con4iOLD.1
    nsyl2
end
