include "wnf.mm"
include "nfnf1.mm"
include "id.mm"
include "wb.mm"
include "weq.mm"
include "biid.mm"
include "2a1i.mm"
include "wl-equsald.mm"

theorem wl-equsal1t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/ x ph -> ( A. x ( x = y -> ph ) <-> ph ) )

  proof
    wph
    vx
    wnf
    #
    wph
    wph
    vx
    vy
    wph
    vx
    nfnf1
    @0
    id
    wph
    wph
    wb
    @0
    vx
    vy
    weq
    wph
    biid
    2a1i
    wl-equsald
end
