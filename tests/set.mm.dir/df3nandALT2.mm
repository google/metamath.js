include "w3nand.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "w3a.mm"
include "df-3nand.mm"
include "imnan.mm"
include "imbi2i.mm"
include "3anass.mm"
include "xchbinxr.mm"
include "3bitri.mm"

theorem df3nandALT2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -/\ ps -/\ ch ) <-> -. ( ph /\ ps /\ ch ) )

  proof
    wph
    wps
    wch
    w3nand
    wph
    wps
    wch
    wn
    wi
    #
    wi
    wph
    wps
    wch
    wa
    #
    wn
    #
    wi
    #
    wph
    wps
    wch
    w3a
    #
    wn
    wph
    wps
    wch
    df-3nand
    @0
    @2
    wph
    wps
    wch
    imnan
    imbi2i
    @3
    wph
    @1
    wa
    @4
    wph
    @1
    imnan
    wph
    wps
    wch
    3anass
    xchbinxr
    3bitri
end
