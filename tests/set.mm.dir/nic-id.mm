include "wnan.mm"
include "nic-ax.mm"
include "nic-idlem2.mm"
include "nic-idlem1.mm"
include "nic-mp.mm"

theorem nic-id
  let wta: wff ta
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ta -/\ ( ta -/\ ta ) )

  proof
    wph
    wps
    wnan
    #
    wps
    wph
    wnan
    #
    @1
    wnan
    wnan
    #
    wch
    wch
    wch
    wnan
    #
    wnan
    #
    wnan
    #
    wps
    wps
    wps
    wnan
    wnan
    #
    wnan
    wta
    wta
    wta
    wnan
    wnan
    #
    @4
    wth
    wth
    wth
    @2
    wch
    @6
    wps
    wps
    wps
    wph
    wth
    nic-ax
    nic-idlem2
    @2
    @3
    wch
    @5
    wps
    @4
    @7
    wnan
    @0
    @1
    @1
    @4
    wta
    nic-idlem1
    nic-idlem2
    nic-mp
end
