include "w3a.mm"
include "wn.mm"
include "wi.mm"
include "w3nand.mm"
include "wnan.mm"
include "wa.mm"
include "3anass.mm"
include "pm4.63.mm"
include "anbi2i.mm"
include "annim.mm"
include "3bitr2i.mm"
include "df-3nand.mm"
include "notbii.mm"
include "nannot.mm"

theorem andnand1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ( ph -/\ ps -/\ ch ) -/\ ( ph -/\ ps -/\ ch ) ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wph
    wps
    wch
    wn
    wi
    #
    wi
    #
    wn
    #
    wph
    wps
    wch
    w3nand
    #
    wn
    @4
    @4
    wnan
    @0
    wph
    wps
    wch
    wa
    #
    wa
    wph
    @1
    wn
    #
    wa
    @3
    wph
    wps
    wch
    3anass
    @6
    @5
    wph
    wps
    wch
    pm4.63
    anbi2i
    wph
    @1
    annim
    3bitr2i
    @4
    @2
    wph
    wps
    wch
    df-3nand
    notbii
    @4
    nannot
    3bitr2i
end
