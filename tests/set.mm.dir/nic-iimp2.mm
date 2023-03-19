include "wnan.mm"
include "nic-isw1.mm"
include "nic-iimp1.mm"

theorem nic-iimp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nic-iimp2.1: |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) )
  assume nic-iimp2.2: |- ( th -/\ ph )


  assert |- ( th -/\ ( ch -/\ ch ) )

  proof
    wch
    wch
    wnan
    #
    wps
    wph
    wth
    @0
    wph
    wps
    wnan
    nic-iimp2.1
    nic-isw1
    nic-iimp2.2
    nic-iimp1
end
