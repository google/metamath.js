include "wi.mm"
include "wn.mm"
include "pm2.21.mm"
include "con4.mm"
include "imim12i.mm"
include "com13.mm"
include "con1d.mm"
include "com12.mm"
include "a1d.mm"
include "ax-1.mm"
include "imim1d.mm"
include "ja.mm"

theorem meredith
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wn
    wth
    wn
    wi
    #
    wi
    #
    wch
    wi
    #
    wta
    wta
    wph
    wi
    #
    wth
    wph
    wi
    #
    wi
    @3
    wn
    #
    @5
    @4
    wth
    @6
    wph
    wth
    wph
    @3
    @2
    wph
    wn
    #
    wth
    wch
    @7
    @0
    @1
    wth
    wch
    wi
    wph
    wps
    pm2.21
    wch
    wth
    con4
    imim12i
    com13
    con1d
    com12
    a1d
    wta
    wth
    wta
    wph
    wta
    wth
    ax-1
    imim1d
    ja
end
