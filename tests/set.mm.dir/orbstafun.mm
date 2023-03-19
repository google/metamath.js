include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cvv.mm"
include "ovexd.mm"
include "csubg.mm"
include "cfv.mm"
include "wer.mm"
include "gastacl.mm"
include "eqger.mm"
include "syl.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "oveq1.mm"
include "wbr.mm"
include "wceq.mm"
include "simpr.mm"
include "wb.mm"
include "cminusg.mm"
include "cplusg.mm"
include "w3a.mm"
include "cgrp.mm"
include "wss.mm"
include "subgrcl.mm"
include "subgss.mm"
include "eqid.mm"
include "eqgval.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "jca.mm"
include "gastacos.mm"
include "syldan.mm"
include "mpbid.mm"
include "qliftfund.mm"

theorem orbstafun
  let vu: setvar u
  let cA: class A
  let c.po: class .(+)
  let c.sm: class .~
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cO: class O
  let cC: class C
  assume gasta.1: |- X = ( Base ` G )
  assume gasta.2: |- H = { u e. X | ( u .(+) A ) = A }
  assume orbsta.r: |- .~ = ( G ~QG H )
  assume orbsta.f: |- F = ran ( k e. X |-> <. [ k ] .~ , ( k .(+) A ) >. )

  disjoint .~ k
  disjoint k u
  disjoint .(+) k
  disjoint .(+) u
  disjoint A k
  disjoint A u
  disjoint G k
  disjoint G u
  disjoint X k
  disjoint X u
  disjoint Y k
  disjoint a b
  disjoint a g
  disjoint a h
  disjoint a k
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint .~ a
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .~ b
  disjoint g h
  disjoint g k
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .~ g
  disjoint h k
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .~ h
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .~ w
  disjoint x y
  disjoint x z
  disjoint .~ x
  disjoint y z
  disjoint .~ y
  disjoint .~ z
  disjoint a u
  disjoint .(+) a
  disjoint b u
  disjoint .(+) b
  disjoint g u
  disjoint .(+) g
  disjoint h u
  disjoint .(+) h
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .(+) w
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A g
  disjoint A h
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G h
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint B g
  disjoint B k
  disjoint B u
  disjoint B x
  disjoint X a
  disjoint X b
  disjoint X g
  disjoint X h
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint F a
  disjoint F b
  disjoint F h
  disjoint F w
  disjoint F z
  disjoint O a
  disjoint O h
  disjoint O k
  disjoint O w
  disjoint O z
  disjoint Y a
  disjoint Y b
  disjoint Y g
  disjoint Y h
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint C u
  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ A e. Y ) -> Fun F )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    cA
    cY
    wcel
    wa
    #
    vk
    vh
    vk
    cv
    #
    cA
    c.po
    co
    #
    vh
    cv
    #
    cA
    c.po
    co
    #
    c.sm
    cF
    cX
    cvv
    orbsta.f
    @0
    @1
    cX
    wcel
    #
    wa
    @1
    cA
    c.po
    ovexd
    @0
    cH
    cG
    csubg
    cfv
    wcel
    #
    cX
    c.sm
    wer
    vu
    cA
    c.po
    cG
    cH
    cX
    cY
    gasta.1
    gasta.2
    gastacl
    #
    c.sm
    cG
    cX
    cH
    gasta.1
    orbsta.r
    eqger
    syl
    cX
    cvv
    wcel
    @0
    cX
    cG
    cbs
    cfv
    cvv
    gasta.1
    cG
    cbs
    fvex
    eqeltri
    a1i
    @1
    @3
    cA
    c.po
    oveq1
    @0
    @1
    @3
    c.sm
    wbr
    #
    wa
    #
    @8
    @2
    @4
    wceq
    #
    @0
    @8
    simpr
    @0
    @8
    @5
    @3
    cX
    wcel
    #
    wa
    @8
    @10
    wb
    @9
    @5
    @11
    @9
    @5
    @11
    @1
    cG
    cminusg
    cfv
    #
    cfv
    @3
    cG
    cplusg
    cfv
    #
    co
    cH
    wcel
    #
    @0
    @8
    @5
    @11
    @14
    w3a
    #
    @0
    @6
    @8
    @15
    wb
    #
    @7
    @6
    cG
    cgrp
    wcel
    cH
    cX
    wss
    @16
    cH
    cG
    subgrcl
    cX
    cH
    cG
    gasta.1
    subgss
    @1
    @3
    @13
    c.sm
    cH
    cG
    @12
    cgrp
    cX
    gasta.1
    @12
    eqid
    @13
    eqid
    orbsta.r
    eqgval
    syl2anc
    syl
    biimpa
    #
    simp1d
    @9
    @5
    @11
    @14
    @17
    simp2d
    jca
    vu
    cA
    @1
    @3
    c.po
    c.sm
    cG
    cH
    cX
    cY
    gasta.1
    gasta.2
    orbsta.r
    gastacos
    syldan
    mpbid
    qliftfund
end
