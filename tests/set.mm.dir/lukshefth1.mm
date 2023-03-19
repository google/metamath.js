include "wnan.mm"
include "lukshef-ax1.mm"
include "nic-mp.mm"

theorem lukshefth1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ta -/\ ps ) -/\ ( ( ph -/\ ta ) -/\ ( ph -/\ ta ) ) ) -/\ ( th -/\ ( th -/\ th ) ) ) -/\ ( ph -/\ ( ps -/\ ch ) ) )

  proof
    wph
    wps
    wch
    wnan
    wnan
    #
    wta
    wta
    wta
    wnan
    wnan
    #
    wta
    wps
    wnan
    wph
    wta
    wnan
    #
    @2
    wnan
    wnan
    #
    wnan
    #
    wnan
    #
    @3
    wth
    wth
    wth
    wnan
    wnan
    #
    wnan
    #
    @0
    wnan
    #
    @8
    wph
    wch
    wps
    wta
    lukshef-ax1
    @7
    @4
    @4
    wnan
    wnan
    #
    @5
    @8
    @8
    wnan
    wnan
    @0
    @0
    @0
    wnan
    wnan
    @1
    @6
    wth
    wta
    wnan
    wta
    wth
    wnan
    #
    @10
    wnan
    wnan
    #
    wnan
    wnan
    @9
    @3
    @3
    @3
    wnan
    wnan
    wta
    wta
    wta
    wth
    lukshef-ax1
    @1
    @11
    @6
    @3
    lukshef-ax1
    nic-mp
    @7
    @4
    @4
    @0
    lukshef-ax1
    nic-mp
    nic-mp
end
