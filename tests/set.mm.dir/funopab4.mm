include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "wss.mm"
include "wfun.mm"
include "simpr.mm"
include "ssopab2i.mm"
include "funopabeq.mm"
include "funss.mm"
include "mp2.mm"

theorem funopab4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- Fun { <. x , y >. | ( ph /\ y = A ) }

  proof
    wph
    vy
    cv
    cA
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @0
    vx
    vy
    copab
    #
    wss
    @3
    wfun
    @2
    wfun
    @1
    @0
    vx
    vy
    wph
    @0
    simpr
    ssopab2i
    vx
    vy
    cA
    funopabeq
    @2
    @3
    funss
    mp2
end
