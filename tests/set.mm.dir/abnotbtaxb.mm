include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "wa.mm"
include "xor3.mm"
include "wi.mm"
include "pm5.1.mm"
include "ibibr.mm"
include "mpbi.mm"
include "mp2an.mm"
include "bitri.mm"
include "mpbir2an.mm"
include "df-xor.mm"
include "mpbir.mm"

theorem abnotbtaxb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume abnotbtaxb.1: |- ph
  assume abnotbtaxb.2: |- -. ps


  assert |- ( ph \/_ ps )

  proof
    wph
    wps
    wxo
    wph
    wps
    wb
    wn
    #
    @0
    wph
    wps
    wn
    #
    abnotbtaxb.1
    abnotbtaxb.2
    @0
    wph
    @1
    wb
    #
    wph
    @1
    wa
    #
    wph
    wps
    xor3
    wph
    @1
    @2
    @3
    wb
    #
    abnotbtaxb.1
    abnotbtaxb.2
    @3
    @2
    wi
    @3
    @4
    wi
    wph
    @1
    pm5.1
    @3
    @2
    ibibr
    mpbi
    mp2an
    bitri
    mpbir2an
    wph
    wps
    df-xor
    mpbir
end
