include "ccj.mm"
include "cjf.mm"
include "cv.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cr.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cjcl.mm"
include "subcl.mm"
include "syl2an.mm"
include "abscld.mm"
include "cjsub.mm"
include "fveq2d.mm"
include "abscjd.mm"
include "eqtr3d.mm"
include "eqle.mm"
include "syl2anc.mm"
include "cn1lem.mm"

theorem cjcn2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. CC /\ x e. RR+ ) -> E. y e. RR+ A. z e. CC ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( * ` z ) - ( * ` A ) ) ) < x ) )

  proof
    vx
    vy
    vz
    cA
    ccj
    cjf
    vz
    cv
    #
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    #
    @0
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cr
    wcel
    @7
    @0
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    wceq
    @7
    @9
    cle
    wbr
    @3
    @6
    @1
    @4
    cc
    wcel
    @5
    cc
    wcel
    @6
    cc
    wcel
    @2
    @0
    cjcl
    cA
    cjcl
    @4
    @5
    subcl
    syl2an
    abscld
    @3
    @8
    ccj
    cfv
    #
    cabs
    cfv
    @7
    @9
    @3
    @10
    @6
    cabs
    @0
    cA
    cjsub
    fveq2d
    @3
    @8
    @0
    cA
    subcl
    abscjd
    eqtr3d
    @7
    @9
    eqle
    syl2anc
    cn1lem
end
