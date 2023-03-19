include "cv.mm"
include "cif.mm"
include "wsbc.mm"
include "sbceq1a.mm"
include "dfsbcq.mm"
include "elimhyp.mm"

theorem elimhyps
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  assume elimhyps.1: |- [. B / x ]. ph


  assert |- [. if ( ph , x , B ) / x ]. ph

  proof
    wph
    wph
    vx
    wph
    vx
    cv
    #
    cB
    cif
    #
    wsbc
    wph
    vx
    cB
    wsbc
    @0
    cB
    wph
    vx
    @1
    sbceq1a
    wph
    vx
    cB
    @1
    dfsbcq
    elimhyps.1
    elimhyp
end
