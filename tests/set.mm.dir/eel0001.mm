include "wi.mm"
include "exp41.mm"
include "mp2.mm"
include "mpsyl.mm"

theorem eel0001
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel0001.1: |- ph
  assume eel0001.2: |- ps
  assume eel0001.3: |- ch
  assume eel0001.4: |- ( th -> ta )
  assume eel0001.5: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) -> et )


  assert |- ( th -> et )

  proof
    wch
    wth
    wta
    wet
    eel0001.3
    eel0001.4
    wph
    wps
    wch
    wta
    wet
    wi
    wi
    eel0001.1
    eel0001.2
    wph
    wps
    wch
    wta
    wet
    eel0001.5
    exp41
    mp2
    mpsyl
end
