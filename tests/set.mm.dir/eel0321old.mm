include "w3a.mm"
include "sylancr.mm"

theorem eel0321old
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel0321old.1: |- ph
  assume eel0321old.2: |- ( ( ps /\ ch /\ th ) -> ta )
  assume eel0321old.3: |- ( ( ph /\ ta ) -> et )


  assert |- ( ( ps /\ ch /\ th ) -> et )

  proof
    wps
    wch
    wth
    w3a
    wph
    wta
    wet
    eel0321old.1
    eel0321old.2
    eel0321old.3
    sylancr
end
