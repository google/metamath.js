include "weq.mm"
include "wi.mm"
include "equcom.mm"
include "imbi1i.mm"
include "albii.mm"

theorem wl-equsalcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( x = y -> ph ) <-> A. x ( y = x -> ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    vy
    vx
    weq
    #
    wph
    wi
    vx
    @0
    @1
    wph
    vx
    vy
    equcom
    imbi1i
    albii
end
