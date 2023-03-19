include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "cmgm.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "ismgmhm.mm"
include "simprl.mm"
include "sylbi.mm"

theorem mgmhmf
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume mgmhmf.b: |- B = ( Base ` S )
  assume mgmhmf.c: |- C = ( Base ` T )


  assert |- ( F e. ( S MgmHom T ) -> F : B --> C )

  proof
    cF
    cS
    cT
    cmgmhm
    co
    wcel
    cS
    cmgm
    wcel
    cT
    cmgm
    wcel
    wa
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
    wa
    wa
    @1
    vx
    vy
    cB
    cC
    @4
    @5
    cS
    cT
    cF
    mgmhmf.b
    mgmhmf.c
    @4
    eqid
    @5
    eqid
    ismgmhm
    @0
    @1
    @6
    simprl
    sylbi
end
