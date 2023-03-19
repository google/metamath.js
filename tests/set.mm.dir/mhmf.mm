include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "cmnd.mm"
include "wa.mm"
include "w3a.mm"
include "eqid.mm"
include "ismhm.mm"
include "simprbi.mm"
include "simp1d.mm"

theorem mhmf
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume mhmf.b: |- B = ( Base ` S )
  assume mhmf.c: |- C = ( Base ` T )


  assert |- ( F e. ( S MndHom T ) -> F : B --> C )

  proof
    cF
    cS
    cT
    cmhm
    co
    wcel
    #
    cB
    cC
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    cF
    cfv
    @2
    cF
    cfv
    @3
    cF
    cfv
    cT
    cplusg
    cfv
    #
    co
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cS
    c0g
    cfv
    #
    cF
    cfv
    cT
    c0g
    cfv
    #
    wceq
    #
    @0
    cS
    cmnd
    wcel
    cT
    cmnd
    wcel
    wa
    @1
    @6
    @9
    w3a
    vx
    vy
    cB
    cC
    @4
    @5
    cS
    cT
    cF
    @8
    @7
    mhmf.b
    mhmf.c
    @4
    eqid
    @5
    eqid
    @7
    eqid
    @8
    eqid
    ismhm
    simprbi
    simp1d
end
