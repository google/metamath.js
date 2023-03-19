include "wi.mm"
include "peirce.mm"
include "ax-mp.mm"

theorem bj-peircei
  let wph: wff ph
  let wps: wff ps
  assume bj-peircei.1: |- ( ( ph -> ps ) -> ph )


  assert |- ph

  proof
    wph
    wps
    wi
    wph
    wi
    wph
    bj-peircei.1
    wph
    wps
    peirce
    ax-mp
end
