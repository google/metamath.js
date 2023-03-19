include "wsbc.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "sbcbii.mm"
include "bnj525.mm"
include "bitri.mm"

theorem bnj91
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cZ: class Z
  assume bnj91.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj91.2: |- Z e. _V

  disjoint A y
  disjoint R y
  disjoint f y
  disjoint x y
  assert |- ( [. Z / y ]. ph <-> ( f ` (/) ) = _pred ( x , A , R ) )

  proof
    wph
    vy
    cZ
    wsbc
    c0
    vf
    cv
    cfv
    cA
    cR
    vx
    cv
    c-bnj14
    wceq
    #
    vy
    cZ
    wsbc
    @0
    wph
    @0
    vy
    cZ
    bnj91.1
    sbcbii
    @0
    vy
    cZ
    bnj91.2
    bnj525
    bitri
end
