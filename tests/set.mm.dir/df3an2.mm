include "w3a.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-3an.mm"
include "df-an.mm"
include "impexp.mm"
include "xchbinx.mm"
include "bitri.mm"

theorem df3an2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> -. ( ph -> ( ps -> -. ch ) ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    #
    wch
    wa
    #
    wph
    wps
    wch
    wn
    #
    wi
    wi
    #
    wn
    wph
    wps
    wch
    df-3an
    @1
    @0
    @2
    wi
    @3
    @0
    wch
    df-an
    wph
    wps
    @2
    impexp
    xchbinx
    bitri
end
