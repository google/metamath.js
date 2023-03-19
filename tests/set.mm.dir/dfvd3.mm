include "wvd3.mm"
include "w3a.mm"
include "wi.mm"
include "df-vd3.mm"
include "wa.mm"
include "df-3an.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"

theorem dfvd3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( (. ph ,. ps ,. ch ->. th ). <-> ( ph -> ( ps -> ( ch -> th ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wvd3
    wph
    wps
    wch
    w3a
    #
    wth
    wi
    #
    wph
    wps
    wch
    wth
    wi
    #
    wi
    wi
    #
    wph
    wps
    wch
    wth
    df-vd3
    @1
    wph
    wps
    wa
    #
    @2
    wi
    #
    @3
    @1
    @4
    wch
    wa
    #
    wth
    wi
    @5
    @0
    @6
    wth
    wph
    wps
    wch
    df-3an
    imbi1i
    @4
    wch
    wth
    impexp
    bitri
    wph
    wps
    @2
    impexp
    bitri
    bitri
end
