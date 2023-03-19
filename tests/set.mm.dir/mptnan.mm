include "wn.mm"
include "imnani.mm"
include "ax-mp.mm"

theorem mptnan
  let wph: wff ph
  let wps: wff ps
  assume mptnan.min: |- ph
  assume mptnan.maj: |- -. ( ph /\ ps )


  assert |- -. ps

  proof
    wph
    wps
    wn
    mptnan.min
    wph
    wps
    mptnan.maj
    imnani
    ax-mp
end
