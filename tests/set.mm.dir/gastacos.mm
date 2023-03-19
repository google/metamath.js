include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "w3a.mm"
include "cgrp.mm"
include "wss.mm"
include "wb.mm"
include "csubg.mm"
include "gastacl.mm"
include "adantr.mm"
include "subgrcl.mm"
include "syl.mm"
include "subgss.mm"
include "eqid.mm"
include "eqgval.mm"
include "syl2anc.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "simpr.mm"
include "biantrurd.mm"
include "simpll.mm"
include "simprl.mm"
include "grpinvcl.mm"
include "simprr.mm"
include "simplr.mm"
include "gaass.mm"
include "syl13anc.mm"
include "eqeq1d.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "cv.mm"
include "oveq1.mm"
include "elrab2.mm"
include "baib.mm"
include "cxp.mm"
include "wf.mm"
include "gaf.mm"
include "fovrnd.mm"
include "gacan.mm"
include "3bitr4d.mm"
include "3bitr2d.mm"

theorem gastacos
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
  let c.sm: class .~
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cO: class O
  assume gasta.1: |- X = ( Base ` G )
  assume gasta.2: |- H = { u e. X | ( u .(+) A ) = A }
  assume orbsta.r: |- .~ = ( G ~QG H )

  disjoint .(+) u
  disjoint A u
  disjoint G u
  disjoint B u
  disjoint X u
  disjoint C u
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
  disjoint .~ k
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
  disjoint k u
  disjoint .(+) k
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
  disjoint A k
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint B g
  disjoint B k
  disjoint B x
  disjoint X a
  disjoint X b
  disjoint X g
  disjoint X h
  disjoint X k
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
  disjoint Y k
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( ( .(+) e. ( G GrpAct Y ) /\ A e. Y ) /\ ( B e. X /\ C e. X ) ) -> ( B .~ C <-> ( B .(+) A ) = ( C .(+) A ) ) )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cA
    cY
    wcel
    #
    wa
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    wa
    #
    wa
    #
    cB
    cC
    c.sm
    wbr
    #
    @5
    cB
    cG
    cminusg
    cfv
    #
    cfv
    #
    cC
    cG
    cplusg
    cfv
    #
    co
    #
    cH
    wcel
    #
    wa
    #
    @12
    cB
    cA
    c.po
    co
    cC
    cA
    c.po
    co
    #
    wceq
    #
    @6
    @7
    @3
    @4
    @12
    w3a
    #
    @13
    @6
    cG
    cgrp
    wcel
    #
    cH
    cX
    wss
    #
    @7
    @16
    wb
    @6
    cH
    cG
    csubg
    cfv
    wcel
    #
    @17
    @2
    @19
    @5
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
    adantr
    #
    cH
    cG
    subgrcl
    syl
    #
    @6
    @19
    @18
    @20
    cX
    cH
    cG
    gasta.1
    subgss
    syl
    cB
    cC
    @10
    c.sm
    cH
    cG
    @8
    cgrp
    cX
    gasta.1
    @8
    eqid
    #
    @10
    eqid
    #
    orbsta.r
    eqgval
    syl2anc
    @3
    @4
    @12
    df-3an
    syl6bb
    @6
    @5
    @12
    @2
    @5
    simpr
    biantrurd
    @6
    @11
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @9
    @14
    c.po
    co
    #
    cA
    wceq
    #
    @12
    @15
    @6
    @24
    @26
    cA
    @6
    @0
    @9
    cX
    wcel
    #
    @4
    @1
    @24
    @26
    wceq
    @0
    @1
    @5
    simpll
    #
    @6
    @17
    @3
    @28
    @21
    @2
    @3
    @4
    simprl
    #
    cX
    cG
    @8
    cB
    gasta.1
    @22
    grpinvcl
    syl2anc
    #
    @2
    @3
    @4
    simprr
    #
    @0
    @1
    @5
    simplr
    #
    @9
    cC
    cA
    @10
    c.po
    cG
    cX
    cY
    gasta.1
    @23
    gaass
    syl13anc
    eqeq1d
    @6
    @11
    cX
    wcel
    #
    @12
    @25
    wb
    @6
    @17
    @28
    @4
    @34
    @21
    @31
    @32
    cX
    @10
    cG
    @9
    cC
    gasta.1
    @23
    grpcl
    syl3anc
    @12
    @34
    @25
    vu
    cv
    #
    cA
    c.po
    co
    #
    cA
    wceq
    @25
    vu
    @11
    cX
    cH
    @35
    @11
    wceq
    @36
    @24
    cA
    @35
    @11
    cA
    c.po
    oveq1
    eqeq1d
    gasta.2
    elrab2
    baib
    syl
    @6
    @0
    @3
    @1
    @14
    cY
    wcel
    @15
    @27
    wb
    @29
    @30
    @33
    @6
    cC
    cA
    cY
    cX
    cY
    c.po
    @6
    @0
    cX
    cY
    cxp
    cY
    c.po
    wf
    @29
    c.po
    cG
    cX
    cY
    gasta.1
    gaf
    syl
    @32
    @33
    fovrnd
    cB
    cA
    @14
    c.po
    cG
    @8
    cX
    cY
    gasta.1
    @22
    gacan
    syl13anc
    3bitr4d
    3bitr2d
end
