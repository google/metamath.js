include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnp.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "wceq.mm"
include "cmpt.mm"
include "cnpfval.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "eqid.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem cnpval
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let cF: class F

  disjoint f x
  disjoint f y
  disjoint J f
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K f
  disjoint K x
  disjoint K y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint P f
  disjoint P x
  disjoint P y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint g j
  disjoint g k
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j k
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K j
  disjoint K k
  disjoint K v
  disjoint K w
  disjoint X j
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint P v
  disjoint Y j
  disjoint Y k
  disjoint Y v
  disjoint Y w
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ P e. X ) -> ( ( J CnP K ) ` P ) = { f e. ( Y ^m X ) | A. y e. K ( ( f ` P ) e. y -> E. x e. J ( P e. x /\ ( f " x ) C_ y ) ) } )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    cP
    vf
    cv
    #
    cfv
    #
    vy
    cv
    #
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    @5
    @9
    cima
    @7
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    #
    wceq
    @0
    @1
    wa
    #
    @2
    @4
    cP
    vv
    cX
    vv
    cv
    #
    @5
    cfv
    #
    @7
    wcel
    #
    @19
    @9
    wcel
    #
    @11
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    vf
    @16
    crab
    #
    cmpt
    #
    cfv
    @17
    @18
    cP
    @3
    @28
    vv
    vy
    vx
    vf
    cJ
    cK
    cX
    cY
    cnpfval
    fveq1d
    vv
    cP
    @27
    @17
    cX
    @28
    @19
    cP
    wceq
    #
    @26
    @15
    vf
    @16
    @29
    @25
    @14
    vy
    cK
    @29
    @21
    @8
    @24
    @13
    @29
    @20
    @6
    @7
    @19
    cP
    @5
    fveq2
    eleq1d
    @29
    @23
    @12
    vx
    cJ
    @29
    @22
    @10
    @11
    @19
    cP
    @9
    eleq1
    anbi1d
    rexbidv
    imbi12d
    ralbidv
    rabbidv
    @28
    eqid
    @15
    vf
    @16
    cY
    cX
    cmap
    ovex
    rabex
    fvmpt
    sylan9eq
    3impa
end
