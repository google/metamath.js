include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cmgmhm.mm"
include "ismhm.mm"
include "df-3an.mm"
include "cmgm.mm"
include "mndmgm.mm"
include "anim12i.mm"
include "biantrurd.mm"
include "ismgmhm.mm"
include "syl6bbr.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem ismhm0
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume ismhm0.b: |- B = ( Base ` S )
  assume ismhm0.c: |- C = ( Base ` T )
  assume ismhm0.p: |- .+ = ( +g ` S )
  assume ismhm0.q: |- .+^ = ( +g ` T )
  assume ismhm0.z: |- .0. = ( 0g ` S )
  assume ismhm0.y: |- Y = ( 0g ` T )


  assert |- ( F e. ( S MndHom T ) <-> ( ( S e. Mnd /\ T e. Mnd ) /\ ( F e. ( S MgmHom T ) /\ ( F ` .0. ) = Y ) ) )

  proof
    cF
    cS
    cT
    cmhm
    co
    wcel
    cS
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
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
    c.pl
    co
    cF
    cfv
    @4
    cF
    cfv
    @5
    cF
    cfv
    c.pd
    co
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    #
    c.0
    cF
    cfv
    cY
    wceq
    #
    w3a
    #
    wa
    @2
    cF
    cS
    cT
    cmgmhm
    co
    wcel
    #
    @7
    wa
    #
    wa
    vx
    vy
    cB
    cC
    c.pl
    c.pd
    cS
    cT
    cF
    cY
    c.0
    ismhm0.b
    ismhm0.c
    ismhm0.p
    ismhm0.q
    ismhm0.z
    ismhm0.y
    ismhm
    @2
    @8
    @10
    @8
    @3
    @6
    wa
    #
    @7
    wa
    @2
    @10
    @3
    @6
    @7
    df-3an
    @2
    @11
    @9
    @7
    @2
    @11
    cS
    cmgm
    wcel
    #
    cT
    cmgm
    wcel
    #
    wa
    #
    @11
    wa
    @9
    @2
    @14
    @11
    @0
    @12
    @1
    @13
    cS
    mndmgm
    cT
    mndmgm
    anim12i
    biantrurd
    vx
    vy
    cB
    cC
    c.pl
    c.pd
    cS
    cT
    cF
    ismhm0.b
    ismhm0.c
    ismhm0.p
    ismhm0.q
    ismgmhm
    syl6bbr
    anbi1d
    syl5bb
    pm5.32i
    bitri
end
