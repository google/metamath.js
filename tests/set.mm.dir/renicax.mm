include "wnan.mm"
include "lukshefth1.mm"
include "lukshefth2.mm"
include "nic-mp.mm"
include "lukshef-ax1.mm"

theorem renicax
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) )

  proof
    wta
    wta
    wta
    wnan
    wnan
    #
    wth
    wch
    wnan
    wph
    wth
    wnan
    #
    @1
    wnan
    wnan
    #
    wnan
    #
    wph
    wch
    wps
    wnan
    wnan
    #
    wnan
    #
    @4
    @3
    wnan
    #
    @6
    @4
    @2
    @0
    wnan
    #
    wnan
    #
    @5
    @5
    @7
    @4
    wnan
    @8
    @8
    wph
    wch
    wps
    wta
    wth
    lukshefth1
    @4
    @7
    lukshefth2
    nic-mp
    @3
    @7
    @7
    wnan
    wnan
    @8
    @5
    @5
    wnan
    wnan
    @4
    @4
    @4
    wnan
    wnan
    @2
    @0
    lukshefth2
    @3
    @7
    @7
    @4
    lukshef-ax1
    nic-mp
    nic-mp
    @4
    @3
    lukshefth2
    nic-mp
end
