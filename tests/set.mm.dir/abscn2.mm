include "cabs.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "absf.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "cv.mm"
include "abs2difabs.mm"
include "cn1lem.mm"

theorem abscn2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. CC /\ x e. RR+ ) -> E. y e. RR+ A. z e. CC ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( abs ` z ) - ( abs ` A ) ) ) < x ) )

  proof
    vx
    vy
    vz
    cA
    cabs
    cc
    cr
    cabs
    wf
    cr
    cc
    wss
    cc
    cc
    cabs
    wf
    absf
    ax-resscn
    cc
    cr
    cc
    cabs
    fss
    mp2an
    vz
    cv
    cA
    abs2difabs
    cn1lem
end
