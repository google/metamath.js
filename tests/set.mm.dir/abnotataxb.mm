include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "pm3.2i.mm"
include "olci.mm"
include "xor.mm"
include "mpbir.mm"
include "df-xor.mm"

theorem abnotataxb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume abnotataxb.1: |- -. ph
  assume abnotataxb.2: |- ps


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
    wa
    #
    wps
    wph
    wn
    #
    wa
    #
    wo
    @3
    @1
    wps
    @2
    abnotataxb.2
    abnotataxb.1
    pm3.2i
    olci
    wph
    wps
    xor
    mpbir
    wph
    wps
    df-xor
    mpbir
end
