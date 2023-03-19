include "cv.mm"
include "co.mm"
include "wceq.mm"
include "oveqd.mm"
include "adantr.mm"

theorem oveqdr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  assume oveqdr.1: |- ( ph -> F = G )


  assert |- ( ( ph /\ ps ) -> ( x F y ) = ( x G y ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    @0
    @1
    cG
    co
    wceq
    wps
    wph
    cF
    cG
    @0
    @1
    oveqdr.1
    oveqd
    adantr
end
