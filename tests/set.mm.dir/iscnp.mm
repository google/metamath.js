include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
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
include "wf.mm"
include "cnpval.mm"
include "eleq2d.mm"
include "wb.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "toponmax.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "3adant3.mm"
include "bitrd.mm"

theorem iscnp
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint Y x
  disjoint Y y
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint J f
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
  disjoint K f
  disjoint K j
  disjoint K k
  disjoint K v
  disjoint K w
  disjoint X f
  disjoint X j
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint F f
  disjoint P f
  disjoint P v
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y v
  disjoint Y w
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ P e. X ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. K ( ( F ` P ) e. y -> E. x e. J ( P e. x /\ ( F " x ) C_ y ) ) ) ) )

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
    w3a
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    #
    wcel
    cF
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
    #
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
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cP
    cF
    cfv
    #
    @7
    wcel
    #
    @10
    cF
    @9
    cima
    #
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
    wa
    #
    @3
    @4
    @18
    cF
    vx
    vy
    cP
    vf
    cJ
    cK
    cX
    cY
    cnpval
    eleq2d
    @0
    @1
    @19
    @29
    wb
    @2
    @19
    cF
    @17
    wcel
    #
    @28
    wa
    @0
    @1
    wa
    #
    @29
    @16
    @28
    vf
    cF
    @17
    @5
    cF
    wceq
    #
    @15
    @27
    vy
    cK
    @32
    @8
    @22
    @14
    @26
    @32
    @6
    @21
    @7
    cP
    @5
    cF
    fveq1
    eleq1d
    @32
    @13
    @25
    vx
    cJ
    @32
    @12
    @24
    @10
    @32
    @11
    @23
    @7
    @5
    cF
    @9
    imaeq1
    sseq1d
    anbi2d
    rexbidv
    imbi12d
    ralbidv
    elrab
    @31
    @30
    @20
    @28
    @1
    cY
    cK
    wcel
    cX
    cJ
    wcel
    @30
    @20
    wb
    @0
    cY
    cK
    toponmax
    cX
    cJ
    toponmax
    cY
    cX
    cF
    cK
    cJ
    elmapg
    syl2anr
    anbi1d
    syl5bb
    3adant3
    bitrd
end
