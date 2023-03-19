include "wsbc.mm"
include "wn.mm"
include "cv.mm"
include "wne.mm"
include "wceq.mm"
include "sbceq1a.mm"
include "biimprcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem pm13.14
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( ( [. A / x ]. ph /\ -. ph ) -> x =/= A )

  proof
    wph
    vx
    cA
    wsbc
    #
    wph
    wn
    vx
    cv
    #
    cA
    wne
    @0
    wph
    @1
    cA
    @1
    cA
    wceq
    wph
    @0
    wph
    vx
    cA
    sbceq1a
    biimprcd
    necon3bd
    imp
end
