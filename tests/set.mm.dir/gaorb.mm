include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "w3a.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq12.mm"
include "sylan.mm"
include "rexbidv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cpr.mm"
include "wss.mm"
include "copab.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "brab2a.mm"
include "df-3an.mm"
include "bitr4i.mm"

theorem gaorb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let c.sm: class .~
  let vg: setvar g
  let vh: setvar h
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cG: class G
  assume gaorb.1: |- .~ = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint g h
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B g
  disjoint B h
  disjoint B x
  disjoint B y
  disjoint .~ h
  disjoint .(+) g
  disjoint .(+) h
  disjoint .(+) x
  disjoint .(+) y
  disjoint X g
  disjoint X h
  disjoint X x
  disjoint X y
  disjoint Y h
  disjoint Y x
  disjoint Y y
  disjoint f h
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint G f
  disjoint h k
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint G h
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint G k
  disjoint u v
  disjoint u w
  disjoint G u
  disjoint v w
  disjoint G v
  disjoint G w
  disjoint .~ f
  disjoint .~ k
  disjoint .~ u
  disjoint .~ v
  disjoint .~ w
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint .(+) f
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint k x
  disjoint k y
  disjoint .(+) k
  disjoint u x
  disjoint u y
  disjoint .(+) u
  disjoint v x
  disjoint v y
  disjoint .(+) v
  disjoint w x
  disjoint w y
  disjoint .(+) w
  disjoint X f
  disjoint X k
  disjoint Y f
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  assert |- ( A .~ B <-> ( A e. Y /\ B e. Y /\ E. h e. X ( h .(+) A ) = B ) )

  proof
    cA
    cB
    c.sm
    wbr
    cA
    cY
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    vh
    cv
    #
    cA
    c.po
    co
    #
    cB
    wceq
    #
    vh
    cX
    wrex
    #
    wa
    @0
    @1
    @5
    w3a
    vg
    cv
    #
    vx
    cv
    #
    c.po
    co
    #
    vy
    cv
    #
    wceq
    #
    vg
    cX
    wrex
    #
    @5
    vx
    vy
    cA
    cB
    cY
    cY
    c.sm
    @7
    cA
    wceq
    #
    @9
    cB
    wceq
    #
    wa
    #
    @11
    @6
    cA
    c.po
    co
    #
    cB
    wceq
    #
    vg
    cX
    wrex
    @5
    @14
    @10
    @16
    vg
    cX
    @12
    @8
    @15
    wceq
    @13
    @10
    @16
    wb
    @7
    cA
    @6
    c.po
    oveq2
    @8
    @15
    @9
    cB
    eqeq12
    sylan
    rexbidv
    @16
    @4
    vg
    vh
    cX
    @6
    @2
    wceq
    @15
    @3
    cB
    @6
    @2
    cA
    c.po
    oveq1
    eqeq1d
    cbvrexv
    syl6bb
    c.sm
    @7
    @9
    cpr
    cY
    wss
    #
    @11
    wa
    #
    vx
    vy
    copab
    @7
    cY
    wcel
    @9
    cY
    wcel
    wa
    #
    @11
    wa
    #
    vx
    vy
    copab
    gaorb.1
    @20
    @18
    vx
    vy
    @19
    @17
    @11
    @7
    @9
    cY
    vx
    vex
    vy
    vex
    prss
    anbi1i
    opabbii
    eqtr4i
    brab2a
    @0
    @1
    @5
    df-3an
    bitr4i
end
