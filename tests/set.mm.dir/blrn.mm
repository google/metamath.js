include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cxp.mm"
include "cpw.mm"
include "cbl.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "blf.mm"
include "ffn.mm"
include "ovelrn.mm"
include "3syl.mm"

theorem blrn
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cR: class R
  let cP: class P
  let cS: class S

  disjoint r x
  disjoint A r
  disjoint A x
  disjoint D r
  disjoint D x
  disjoint X r
  disjoint X x
  disjoint r y
  disjoint x y
  disjoint A y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint P r
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S x
  disjoint X y
  disjoint X z
  assert |- ( D e. ( *Met ` X ) -> ( A e. ran ( ball ` D ) <-> E. x e. X E. r e. RR* A = ( x ( ball ` D ) r ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cX
    cxr
    cxp
    #
    cX
    cpw
    #
    cD
    cbl
    cfv
    #
    wf
    @2
    @0
    wfn
    cA
    @2
    crn
    wcel
    cA
    vx
    cv
    vr
    cv
    @2
    co
    wceq
    vr
    cxr
    wrex
    vx
    cX
    wrex
    wb
    cD
    cX
    blf
    @0
    @1
    @2
    ffn
    vx
    vr
    cX
    cxr
    cA
    @2
    ovelrn
    3syl
end
