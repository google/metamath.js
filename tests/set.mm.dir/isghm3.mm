include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cgrp.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "isghm.mm"
include "baib.mm"

theorem isghm3
  let vv: setvar v
  let vu: setvar u
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vf: setvar f
  assume isghm.w: |- X = ( Base ` S )
  assume isghm.x: |- Y = ( Base ` T )
  assume isghm.a: |- .+ = ( +g ` S )
  assume isghm.b: |- .+^ = ( +g ` T )

  disjoint u v
  disjoint S u
  disjoint S v
  disjoint T u
  disjoint T v
  disjoint X u
  disjoint X v
  disjoint .+ u
  disjoint .+ v
  disjoint Y u
  disjoint Y v
  disjoint .+^ u
  disjoint .+^ v
  disjoint F u
  disjoint F v
  disjoint s t
  disjoint s w
  disjoint s u
  disjoint s v
  disjoint f s
  disjoint S s
  disjoint t w
  disjoint t u
  disjoint t v
  disjoint f t
  disjoint S t
  disjoint u w
  disjoint v w
  disjoint f w
  disjoint S w
  disjoint f u
  disjoint f v
  disjoint S f
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T f
  disjoint X f
  disjoint X t
  disjoint X s
  disjoint .+ f
  disjoint .+ s
  disjoint .+ t
  disjoint Y f
  disjoint Y s
  disjoint Y t
  disjoint .+^ f
  disjoint .+^ s
  disjoint .+^ t
  disjoint F f
  assert |- ( ( S e. Grp /\ T e. Grp ) -> ( F e. ( S GrpHom T ) <-> ( F : X --> Y /\ A. u e. X A. v e. X ( F ` ( u .+ v ) ) = ( ( F ` u ) .+^ ( F ` v ) ) ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    wa
    cX
    cY
    cF
    wf
    vu
    cv
    #
    vv
    cv
    #
    c.pl
    co
    cF
    cfv
    @0
    cF
    cfv
    @1
    cF
    cfv
    c.pd
    co
    wceq
    vv
    cX
    wral
    vu
    cX
    wral
    wa
    vv
    vu
    c.pl
    c.pd
    cS
    cT
    cF
    cX
    cY
    isghm.w
    isghm.x
    isghm.a
    isghm.b
    isghm
    baib
end
