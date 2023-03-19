include "cre.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "ref.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "resub.mm"
include "fveq2d.mm"
include "wbr.mm"
include "subcl.mm"
include "absrele.mm"
include "syl.mm"
include "eqbrtrrd.mm"
include "cn1lem.mm"

theorem recn2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. CC /\ x e. RR+ ) -> E. y e. RR+ A. z e. CC ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( Re ` z ) - ( Re ` A ) ) ) < x ) )

  proof
    vx
    vy
    vz
    cA
    cre
    cc
    cr
    cre
    wf
    cr
    cc
    wss
    cc
    cc
    cre
    wf
    ref
    ax-resscn
    cc
    cr
    cc
    cre
    fss
    mp2an
    vz
    cv
    #
    cc
    wcel
    cA
    cc
    wcel
    wa
    #
    @0
    cA
    cmin
    co
    #
    cre
    cfv
    #
    cabs
    cfv
    #
    @0
    cre
    cfv
    cA
    cre
    cfv
    cmin
    co
    #
    cabs
    cfv
    @2
    cabs
    cfv
    #
    cle
    @1
    @3
    @5
    cabs
    @0
    cA
    resub
    fveq2d
    @1
    @2
    cc
    wcel
    @4
    @6
    cle
    wbr
    @0
    cA
    subcl
    @2
    absrele
    syl
    eqbrtrrd
    cn1lem
end
