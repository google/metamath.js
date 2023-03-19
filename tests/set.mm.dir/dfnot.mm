include "wfal.mm"
include "wn.mm"
include "wi.mm"
include "wb.mm"
include "fal.mm"
include "mtt.mm"
include "ax-mp.mm"

theorem dfnot
  let wph: wff ph


  assert |- ( -. ph <-> ( ph -> F. ) )

  proof
    wfal
    wn
    wph
    wn
    wph
    wfal
    wi
    wb
    fal
    wfal
    wph
    mtt
    ax-mp
end
