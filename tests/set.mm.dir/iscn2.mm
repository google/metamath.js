include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "wa.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "cuni.mm"
include "cmap.mm"
include "crab.mm"
include "df-cn.mm"
include "elmpt2cl.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "toptopon.mm"
include "iscn.mm"
include "syl2anb.mm"
include "biadan2.mm"

theorem iscn2
  let vy: setvar y
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
  let vx: setvar x
  let cP: class P
  assume iscn.1: |- X = U. J
  assume iscn.2: |- Y = U. K

  disjoint J y
  disjoint K y
  disjoint X y
  disjoint F y
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
  disjoint x y
  disjoint J x
  disjoint K f
  disjoint K j
  disjoint K k
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint X f
  disjoint X j
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint F f
  disjoint F x
  disjoint P f
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  assert |- ( F e. ( J Cn K ) <-> ( ( J e. Top /\ K e. Top ) /\ ( F : X --> Y /\ A. y e. K ( `' F " y ) e. J ) ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    cX
    cY
    cF
    wf
    cF
    ccnv
    vy
    cv
    #
    cima
    cJ
    wcel
    vy
    cK
    wral
    wa
    #
    vj
    vk
    ctop
    ctop
    vf
    cv
    ccnv
    @3
    cima
    vj
    cv
    #
    wcel
    vy
    vk
    cv
    #
    wral
    vf
    @6
    cuni
    @5
    cuni
    cmap
    co
    crab
    cJ
    cK
    ccn
    cF
    vy
    vf
    vj
    vk
    df-cn
    elmpt2cl
    @1
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @0
    @4
    wb
    @2
    cJ
    cX
    iscn.1
    toptopon
    cK
    cY
    iscn.2
    toptopon
    vy
    cF
    cJ
    cK
    cX
    cY
    iscn
    syl2anb
    biadan2
end
