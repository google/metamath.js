include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "subgmulgcl.mm"
include "3expa.mm"
include "an32s.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"

theorem cycsubgss
  let vx: setvar x
  let cA: class A
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  assume cycsubg.x: |- X = ( Base ` G )
  assume cycsubg.t: |- .x. = ( .g ` G )
  assume cycsubg.f: |- F = ( x e. ZZ |-> ( x .x. A ) )

  disjoint A x
  disjoint G x
  disjoint S x
  disjoint .x. x
  disjoint X x
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint A m
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint s x
  disjoint A s
  disjoint m u
  disjoint m v
  disjoint G m
  disjoint n u
  disjoint n v
  disjoint G n
  disjoint s u
  disjoint s v
  disjoint G s
  disjoint u v
  disjoint u x
  disjoint G u
  disjoint v x
  disjoint G v
  disjoint X m
  disjoint X n
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F v
  assert |- ( ( S e. ( SubGrp ` G ) /\ A e. S ) -> ran F C_ S )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cA
    cS
    wcel
    #
    wa
    #
    cz
    cS
    cF
    wf
    cF
    crn
    cS
    wss
    @2
    vx
    cz
    vx
    cv
    #
    cA
    c.x
    co
    #
    cS
    cF
    @0
    @3
    cz
    wcel
    #
    @1
    @4
    cS
    wcel
    #
    @0
    @5
    @1
    @6
    cS
    c.x
    cG
    @3
    cA
    cycsubg.t
    subgmulgcl
    3expa
    an32s
    cycsubg.f
    fmptd
    cz
    cS
    cF
    frn
    syl
end
