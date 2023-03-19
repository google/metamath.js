include "wi.mm"
include "wn.mm"
include "notnotr.mm"
include "imim1i.mm"
include "con1d.mm"

theorem con3ALT2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) )

  proof
    wph
    wps
    wi
    wph
    wn
    #
    wps
    @0
    wn
    wph
    wps
    wph
    notnotr
    imim1i
    con1d
end
