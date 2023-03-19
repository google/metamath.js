include "dfvd3ani.mm"
include "eel0321old.mm"
include "dfvd3anir.mm"

theorem el0321old
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume el0321old.1: |- ph
  assume el0321old.2: |- (. (. ps ,. ch ,. th ). ->. ta ).
  assume el0321old.3: |- ( ( ph /\ ta ) -> et )


  assert |- (. (. ps ,. ch ,. th ). ->. et ).

  proof
    wps
    wch
    wth
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    el0321old.1
    wps
    wch
    wth
    wta
    el0321old.2
    dfvd3ani
    el0321old.3
    eel0321old
    dfvd3anir
end
