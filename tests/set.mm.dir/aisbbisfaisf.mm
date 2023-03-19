include "wfal.mm"
include "bitri.mm"

theorem aisbbisfaisf
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aisbbisfaisf.1: |- ( ph <-> ps )
  assume aisbbisfaisf.2: |- ( ps <-> F. )


  assert |- ( ph <-> F. )

  proof
    wph
    wps
    wfal
    aisbbisfaisf.1
    aisbbisfaisf.2
    bitri
end
