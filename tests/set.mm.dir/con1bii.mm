include "wn.mm"
include "notnotb.mm"
include "xchbinx.mm"
include "bicomi.mm"

theorem con1bii
  let wph: wff ph
  let wps: wff ps
  assume con1bii.1: |- ( -. ph <-> ps )


  assert |- ( -. ps <-> ph )

  proof
    wph
    wps
    wn
    wph
    wph
    wn
    wps
    wph
    notnotb
    con1bii.1
    xchbinx
    bicomi
end
