include "wnan.mm"
include "nic-ax.mm"
include "nic-imp.mm"
include "nic-mp.mm"

theorem nic-idlem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume nic-idlem2.1: |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) )


  assert |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et )

  proof
    wet
    wph
    wch
    wps
    wnan
    wnan
    #
    wth
    wnan
    #
    wnan
    wth
    wta
    wta
    wta
    wnan
    wnan
    #
    wnan
    #
    wet
    wnan
    #
    @4
    nic-idlem2.1
    @3
    @1
    @1
    wet
    @0
    wph
    wch
    wnan
    wph
    wph
    wnan
    #
    @5
    wnan
    wnan
    @2
    wth
    wph
    wps
    wch
    wph
    wta
    nic-ax
    nic-imp
    nic-imp
    nic-mp
end
