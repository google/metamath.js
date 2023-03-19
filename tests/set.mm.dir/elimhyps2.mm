include "wsbc.mm"
include "cif.mm"
include "dfsbcq.mm"
include "elimhyp.mm"

theorem elimhyps2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elimhyps2.1: |- [. B / x ]. ph


  assert |- [. if ( [. A / x ]. ph , A , B ) / x ]. ph

  proof
    wph
    vx
    cA
    wsbc
    #
    wph
    vx
    @0
    cA
    cB
    cif
    #
    wsbc
    wph
    vx
    cB
    wsbc
    cA
    cB
    wph
    vx
    cA
    @1
    dfsbcq
    wph
    vx
    cB
    @1
    dfsbcq
    elimhyps2.1
    elimhyp
end
