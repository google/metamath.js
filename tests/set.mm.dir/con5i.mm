include "wn.mm"
include "wb.mm"
include "wi.mm"
include "con5.mm"
include "ax-mp.mm"

theorem con5i
  let wph: wff ph
  let wps: wff ps
  assume con5i.1: |- ( ph <-> -. ps )


  assert |- ( -. ph -> ps )

  proof
    wph
    wps
    wn
    wb
    wph
    wn
    wps
    wi
    con5i.1
    wph
    wps
    con5
    ax-mp
end
