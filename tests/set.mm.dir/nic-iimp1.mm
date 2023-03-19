include "wnan.mm"
include "nic-imp.mm"
include "nic-mp.mm"
include "nic-isw1.mm"

theorem nic-iimp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nic-iimp1.1: |- ( ph -/\ ( ch -/\ ps ) )
  assume nic-iimp1.2: |- ( th -/\ ch )


  assert |- ( th -/\ ph )

  proof
    wth
    wph
    wth
    wch
    wnan
    wph
    wth
    wnan
    #
    @0
    nic-iimp1.2
    wph
    wps
    wch
    wth
    nic-iimp1.1
    nic-imp
    nic-mp
    nic-isw1
end
