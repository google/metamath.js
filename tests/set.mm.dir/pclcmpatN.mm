include "cal.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "cfn.mm"
include "wrex.mm"
include "cpw.mm"
include "cin.mm"
include "ciun.mm"
include "pclfinN.mm"
include "eleq2d.mm"
include "eliun.mm"
include "syl6bb.mm"
include "elin.mm"
include "elpwi.mm"
include "anim2i.mm"
include "sylbi.mm"
include "anim1i.mm"
include "anass.mm"
include "sylib.mm"
include "reximi2.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem pclcmpatN
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cU: class U
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  assume pclfin.a: |- A = ( Atoms ` K )
  assume pclfin.c: |- U = ( PCl ` K )

  disjoint A y
  disjoint U y
  disjoint K y
  disjoint X y
  disjoint P y
  disjoint p q
  disjoint p r
  disjoint p v
  disjoint p w
  disjoint p y
  disjoint A p
  disjoint q r
  disjoint q v
  disjoint q w
  disjoint q y
  disjoint A q
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint v w
  disjoint v y
  disjoint A v
  disjoint w y
  disjoint A w
  disjoint U p
  disjoint U q
  disjoint U r
  disjoint U v
  disjoint U w
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K v
  disjoint K w
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X v
  disjoint X w
  assert |- ( ( K e. AtLat /\ X C_ A /\ P e. ( U ` X ) ) -> E. y e. Fin ( y C_ X /\ P e. ( U ` y ) ) )

  proof
    cK
    cal
    wcel
    #
    cX
    cA
    wss
    #
    cP
    cX
    cU
    cfv
    #
    wcel
    #
    vy
    cv
    #
    cX
    wss
    #
    cP
    @4
    cU
    cfv
    #
    wcel
    #
    wa
    #
    vy
    cfn
    wrex
    #
    @0
    @1
    wa
    #
    @3
    @7
    vy
    cfn
    cX
    cpw
    #
    cin
    #
    wrex
    #
    @9
    @10
    @3
    cP
    vy
    @12
    @6
    ciun
    #
    wcel
    @13
    @10
    @2
    @14
    cP
    vy
    cA
    cU
    cK
    cX
    pclfin.a
    pclfin.c
    pclfinN
    eleq2d
    vy
    cP
    @12
    @6
    eliun
    syl6bb
    @7
    @8
    vy
    @12
    cfn
    @4
    @12
    wcel
    #
    @7
    wa
    @4
    cfn
    wcel
    #
    @5
    wa
    #
    @7
    wa
    @16
    @8
    wa
    @15
    @17
    @7
    @15
    @16
    @4
    @11
    wcel
    #
    wa
    @17
    @4
    cfn
    @11
    elin
    @18
    @5
    @16
    @4
    cX
    elpwi
    anim2i
    sylbi
    anim1i
    @16
    @5
    @7
    anass
    sylib
    reximi2
    syl6bi
    3impia
end
