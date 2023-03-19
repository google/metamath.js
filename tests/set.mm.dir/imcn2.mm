include "cim.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "imf.mm"
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
include "imsub.mm"
include "fveq2d.mm"
include "wbr.mm"
include "subcl.mm"
include "absimle.mm"
include "syl.mm"
include "eqbrtrrd.mm"
include "cn1lem.mm"

theorem imcn2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. CC /\ x e. RR+ ) -> E. y e. RR+ A. z e. CC ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( Im ` z ) - ( Im ` A ) ) ) < x ) )

  proof
    vx
    vy
    vz
    cA
    cim
    cc
    cr
    cim
    wf
    cr
    cc
    wss
    cc
    cc
    cim
    wf
    imf
    ax-resscn
    cc
    cr
    cc
    cim
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
    cim
    cfv
    #
    cabs
    cfv
    #
    @0
    cim
    cfv
    cA
    cim
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
    imsub
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
    absimle
    syl
    eqbrtrrd
    cn1lem
end
