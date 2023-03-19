include "wn.mm"
include "wi.mm"
include "luk-2.mm"
include "luklem3.mm"
include "ax-mp.mm"
include "luk-1.mm"
include "luklem1.mm"

theorem luklem4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps )

  proof
    wph
    wn
    wph
    wi
    wph
    wi
    #
    wps
    wi
    #
    wps
    wn
    #
    wps
    wi
    #
    wps
    @2
    @0
    wi
    #
    @1
    @3
    wi
    @0
    wn
    @0
    wi
    @0
    wi
    #
    @4
    @0
    luk-2
    @0
    @5
    @4
    wi
    wph
    luk-2
    @0
    @0
    @0
    @2
    luklem3
    ax-mp
    ax-mp
    @2
    @0
    wps
    luk-1
    ax-mp
    wps
    luk-2
    luklem1
end
