include "wn.mm"
include "wi.mm"
include "ax-luk3.mm"
include "ax-luk1.mm"
include "wl-syl5.mm"
include "ax-luk2.mm"
include "wl-syl6.mm"

theorem wl-ax3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )

  proof
    wph
    wn
    #
    wps
    wn
    #
    wi
    #
    wps
    @0
    wph
    wi
    #
    wph
    wps
    @1
    wph
    wi
    @2
    @3
    wps
    wph
    ax-luk3
    @0
    @1
    wph
    ax-luk1
    wl-syl5
    wph
    ax-luk2
    wl-syl6
end
