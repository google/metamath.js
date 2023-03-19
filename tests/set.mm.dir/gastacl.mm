include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "wral.mm"
include "cminusg.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "c0g.mm"
include "cgrp.mm"
include "gagrp.mm"
include "adantr.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "gagrpid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "simpll.mm"
include "simpr.mm"
include "sylib.mm"
include "simpld.mm"
include "adantrr.mm"
include "simprr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simplr.mm"
include "gaass.mm"
include "syl13anc.mm"
include "simprd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "wb.mm"
include "gacan.mm"
include "mpbid.mm"
include "jca.mm"
include "w3a.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem gastacl
  let vu: setvar u
  let cA: class A
  let c.po: class .(+)
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
  let c.sm: class .~
  let cB: class B
  let cF: class F
  let cO: class O
  let cC: class C
  assume gasta.1: |- X = ( Base ` G )
  assume gasta.2: |- H = { u e. X | ( u .(+) A ) = A }

  disjoint .(+) u
  disjoint A u
  disjoint G u
  disjoint X u
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
  disjoint B u
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
  disjoint C u
  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ A e. Y ) -> H e. ( SubGrp ` G ) )

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
    cH
    cG
    csubg
    cfv
    wcel
    #
    cH
    cX
    wss
    #
    cH
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cH
    wcel
    #
    vy
    cH
    wral
    #
    @6
    cG
    cminusg
    cfv
    #
    cfv
    #
    cH
    wcel
    #
    wa
    #
    vx
    cH
    wral
    #
    @4
    @2
    cH
    vu
    cv
    #
    cA
    c.po
    co
    #
    cA
    wceq
    #
    vu
    cX
    crab
    cX
    gasta.2
    @19
    vu
    cX
    ssrab2
    eqsstri
    a1i
    @2
    cG
    c0g
    cfv
    #
    cH
    wcel
    #
    @5
    @2
    @20
    cX
    wcel
    #
    @20
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @21
    @2
    cG
    cgrp
    wcel
    #
    @22
    @0
    @25
    @1
    c.po
    cG
    cY
    gagrp
    #
    adantr
    #
    cX
    cG
    @20
    gasta.1
    @20
    eqid
    #
    grpidcl
    syl
    cA
    c.po
    cG
    cY
    @20
    @28
    gagrpid
    @19
    @24
    vu
    @20
    cX
    cH
    @17
    @20
    wceq
    @18
    @23
    cA
    @17
    @20
    cA
    c.po
    oveq1
    eqeq1d
    gasta.2
    elrab2
    sylanbrc
    cH
    @20
    ne0i
    syl
    @2
    @15
    vx
    cH
    @2
    @6
    cH
    wcel
    #
    wa
    #
    @11
    @14
    @30
    @10
    vy
    cH
    @2
    @29
    @7
    cH
    wcel
    #
    @10
    @2
    @29
    @31
    wa
    #
    wa
    #
    @9
    cX
    wcel
    #
    @9
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @10
    @33
    @25
    @6
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    @34
    @33
    @0
    @25
    @0
    @1
    @32
    simpll
    #
    @26
    syl
    @2
    @29
    @37
    @31
    @30
    @37
    @6
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @30
    @29
    @37
    @41
    wa
    @2
    @29
    simpr
    @19
    @41
    vu
    @6
    cX
    cH
    @17
    @6
    wceq
    @18
    @40
    cA
    @17
    @6
    cA
    c.po
    oveq1
    eqeq1d
    gasta.2
    elrab2
    sylib
    #
    simpld
    #
    adantrr
    #
    @33
    @38
    @7
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @33
    @31
    @38
    @46
    wa
    @2
    @29
    @31
    simprr
    @19
    @46
    vu
    @7
    cX
    cH
    @17
    @7
    wceq
    @18
    @45
    cA
    @17
    @7
    cA
    c.po
    oveq1
    eqeq1d
    gasta.2
    elrab2
    sylib
    #
    simpld
    #
    cX
    @8
    cG
    @6
    @7
    gasta.1
    @8
    eqid
    #
    grpcl
    syl3anc
    @33
    @35
    @6
    @45
    c.po
    co
    #
    @40
    cA
    @33
    @0
    @37
    @38
    @1
    @35
    @50
    wceq
    @39
    @44
    @48
    @0
    @1
    @32
    simplr
    @6
    @7
    cA
    @8
    c.po
    cG
    cX
    cY
    gasta.1
    @49
    gaass
    syl13anc
    @33
    @45
    cA
    @6
    c.po
    @33
    @38
    @46
    @47
    simprd
    oveq2d
    @2
    @29
    @41
    @31
    @30
    @37
    @41
    @42
    simprd
    #
    adantrr
    3eqtrd
    @19
    @36
    vu
    @9
    cX
    cH
    @17
    @9
    wceq
    @18
    @35
    cA
    @17
    @9
    cA
    c.po
    oveq1
    eqeq1d
    gasta.2
    elrab2
    sylanbrc
    anassrs
    ralrimiva
    @30
    @13
    cX
    wcel
    #
    @13
    cA
    c.po
    co
    #
    cA
    wceq
    #
    @14
    @30
    @25
    @37
    @52
    @30
    @0
    @25
    @0
    @1
    @29
    simpll
    #
    @26
    syl
    @43
    cX
    cG
    @12
    @6
    gasta.1
    @12
    eqid
    #
    grpinvcl
    syl2anc
    @30
    @41
    @54
    @51
    @30
    @0
    @37
    @1
    @1
    @41
    @54
    wb
    @55
    @43
    @0
    @1
    @29
    simplr
    #
    @57
    @6
    cA
    cA
    c.po
    cG
    @12
    cX
    cY
    gasta.1
    @56
    gacan
    syl13anc
    mpbid
    @19
    @54
    vu
    @13
    cX
    cH
    @17
    @13
    wceq
    @18
    @53
    cA
    @17
    @13
    cA
    c.po
    oveq1
    eqeq1d
    gasta.2
    elrab2
    sylanbrc
    jca
    ralrimiva
    @2
    @25
    @3
    @4
    @5
    @16
    w3a
    wb
    @27
    vx
    vy
    cX
    @8
    cH
    cG
    @12
    gasta.1
    @49
    @56
    issubg2
    syl
    mpbir3and
end
