include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cqs.mm"
include "cec.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfun.mm"
include "orbstafun.mm"
include "wbr.mm"
include "wrex.mm"
include "simpr.mm"
include "adantr.mm"
include "cxp.mm"
include "gaf.mm"
include "fovrnd.mm"
include "eqid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "gaorb.mm"
include "syl3anbrc.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "elecg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "csubg.mm"
include "wer.mm"
include "gastacl.mm"
include "eqger.mm"
include "syl.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "qliftf.mm"
include "mpbid.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "orbstaval.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqeq12d.mm"
include "gastacos.mm"
include "simprl.mm"
include "erth.mm"
include "3bitr2d.mm"
include "biimpd.mm"
include "anassrs.mm"
include "ectocld.mm"
include "ralrimiva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "w3a.mm"
include "vex.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "simp3d.mm"
include "cqg.mm"
include "ecelqsi.mm"
include "adantl.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "imp.mm"
include "syldan.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem orbsta
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.po: class .(+)
  let c.sm: class .~
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume gasta.1: |- X = ( Base ` G )
  assume gasta.2: |- H = { u e. X | ( u .(+) A ) = A }
  assume orbsta.r: |- .~ = ( G ~QG H )
  assume orbsta.f: |- F = ran ( k e. X |-> <. [ k ] .~ , ( k .(+) A ) >. )
  assume orbsta.o: |- O = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint g k
  disjoint g x
  disjoint g y
  disjoint .~ g
  disjoint k x
  disjoint k y
  disjoint .~ k
  disjoint x y
  disjoint .~ x
  disjoint .~ y
  disjoint g u
  disjoint .(+) g
  disjoint k u
  disjoint .(+) k
  disjoint u x
  disjoint u y
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint H x
  disjoint H y
  disjoint A g
  disjoint A k
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint G g
  disjoint G k
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint X g
  disjoint X k
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint O k
  disjoint Y g
  disjoint Y k
  disjoint Y x
  disjoint Y y
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
  disjoint g w
  disjoint g z
  disjoint h k
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .~ h
  disjoint k w
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .~ w
  disjoint x z
  disjoint y z
  disjoint .~ z
  disjoint a u
  disjoint .(+) a
  disjoint b u
  disjoint .(+) b
  disjoint h u
  disjoint .(+) h
  disjoint u w
  disjoint u z
  disjoint .(+) w
  disjoint .(+) z
  disjoint A a
  disjoint A b
  disjoint A h
  disjoint A w
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G h
  disjoint G w
  disjoint G z
  disjoint B g
  disjoint B k
  disjoint B u
  disjoint B x
  disjoint X a
  disjoint X b
  disjoint X h
  disjoint X w
  disjoint X z
  disjoint F a
  disjoint F b
  disjoint F h
  disjoint F w
  disjoint F z
  disjoint O a
  disjoint O h
  disjoint O w
  disjoint O z
  disjoint Y a
  disjoint Y b
  disjoint Y h
  disjoint Y w
  disjoint Y z
  disjoint C u
  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ A e. Y ) -> F : ( X /. .~ ) -1-1-onto-> [ A ] O )

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
    cX
    c.sm
    cqs
    #
    cA
    cO
    cec
    #
    cF
    wf1
    #
    @3
    @4
    cF
    wfo
    #
    @3
    @4
    cF
    wf1o
    @2
    @3
    @4
    cF
    wf
    #
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @8
    @10
    wceq
    #
    wi
    #
    vb
    @3
    wral
    #
    va
    @3
    wral
    @5
    @2
    cF
    wfun
    @7
    vu
    cA
    c.po
    c.sm
    vk
    cF
    cG
    cH
    cX
    cY
    gasta.1
    gasta.2
    orbsta.r
    orbsta.f
    orbstafun
    @2
    vk
    vk
    cv
    #
    cA
    c.po
    co
    #
    c.sm
    cF
    cX
    @4
    orbsta.f
    @2
    @16
    cX
    wcel
    #
    wa
    #
    @17
    @4
    wcel
    #
    cA
    @17
    cO
    wbr
    #
    @19
    @1
    @17
    cY
    wcel
    vh
    cv
    #
    cA
    c.po
    co
    #
    @17
    wceq
    #
    vh
    cX
    wrex
    #
    @21
    @2
    @1
    @18
    @0
    @1
    simpr
    #
    adantr
    #
    @19
    @16
    cA
    cY
    cX
    cY
    c.po
    @2
    cX
    cY
    cxp
    cY
    c.po
    wf
    #
    @18
    @0
    @28
    @1
    c.po
    cG
    cX
    cY
    gasta.1
    gaf
    adantr
    adantr
    @2
    @18
    simpr
    #
    @27
    fovrnd
    @19
    @18
    @17
    @17
    wceq
    #
    @25
    @29
    @17
    eqid
    @24
    @30
    vh
    @16
    cX
    @22
    @16
    wceq
    @23
    @17
    @17
    @22
    @16
    cA
    c.po
    oveq1
    eqeq1d
    rspcev
    sylancl
    vx
    vy
    cA
    @17
    c.po
    cO
    vg
    vh
    cX
    cY
    orbsta.o
    gaorb
    syl3anbrc
    @19
    @17
    cvv
    wcel
    @1
    @20
    @21
    wb
    @16
    cA
    c.po
    ovex
    @27
    @17
    cA
    cO
    cvv
    cY
    elecg
    sylancr
    mpbird
    @2
    cH
    cG
    csubg
    cfv
    wcel
    cX
    c.sm
    wer
    #
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
    c.sm
    cG
    cX
    cH
    gasta.1
    orbsta.r
    eqger
    syl
    #
    cX
    cvv
    wcel
    @2
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
    qliftf
    mpbid
    #
    @2
    @15
    va
    @3
    vz
    cv
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    @11
    wceq
    #
    @35
    @10
    wceq
    #
    wi
    #
    vb
    @3
    wral
    @15
    @2
    vz
    @8
    cX
    c.sm
    @3
    @3
    eqid
    #
    @35
    @8
    wceq
    #
    @39
    @14
    vb
    @3
    @41
    @37
    @12
    @38
    @13
    @41
    @36
    @9
    @11
    @35
    @8
    cF
    fveq2
    eqeq1d
    @35
    @8
    @10
    eqeq1
    imbi12d
    ralbidv
    @2
    @34
    cX
    wcel
    #
    wa
    #
    @39
    vb
    @3
    @36
    vw
    cv
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    wceq
    #
    @35
    @45
    wceq
    #
    wi
    #
    @39
    @43
    vw
    @10
    cX
    c.sm
    @3
    @40
    @45
    @10
    wceq
    #
    @47
    @37
    @48
    @38
    @50
    @46
    @11
    @36
    @45
    @10
    cF
    fveq2
    eqeq2d
    @45
    @10
    @35
    eqeq2
    imbi12d
    @2
    @42
    @44
    cX
    wcel
    #
    @49
    @2
    @42
    @51
    wa
    #
    wa
    #
    @47
    @48
    @53
    @47
    @34
    cA
    c.po
    co
    #
    @44
    cA
    c.po
    co
    #
    wceq
    @34
    @44
    c.sm
    wbr
    @48
    @53
    @36
    @54
    @46
    @55
    @2
    @42
    @36
    @54
    wceq
    @51
    vu
    cA
    @34
    c.po
    c.sm
    vk
    cF
    cG
    cH
    cX
    cY
    gasta.1
    gasta.2
    orbsta.r
    orbsta.f
    orbstaval
    adantrr
    @2
    @51
    @46
    @55
    wceq
    @42
    vu
    cA
    @44
    c.po
    c.sm
    vk
    cF
    cG
    cH
    cX
    cY
    gasta.1
    gasta.2
    orbsta.r
    orbsta.f
    orbstaval
    #
    adantrl
    eqeq12d
    vu
    cA
    @34
    @44
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
    @53
    @34
    @44
    c.sm
    cX
    @2
    @31
    @52
    @32
    adantr
    @2
    @42
    @51
    simprl
    erth
    3bitr2d
    biimpd
    anassrs
    ectocld
    ralrimiva
    ectocld
    ralrimiva
    va
    vb
    @3
    @4
    cF
    dff13
    sylanbrc
    @2
    @7
    @22
    @34
    cF
    cfv
    #
    wceq
    #
    vz
    @3
    wrex
    #
    vh
    @4
    wral
    @6
    @33
    @2
    @59
    vh
    @4
    @2
    @22
    @4
    wcel
    #
    @55
    @22
    wceq
    #
    vw
    cX
    wrex
    #
    @59
    @2
    @60
    wa
    @1
    @22
    cY
    wcel
    #
    @62
    @2
    @60
    @1
    @63
    @62
    w3a
    #
    @2
    @60
    cA
    @22
    cO
    wbr
    #
    @64
    @2
    @22
    cvv
    wcel
    @1
    @60
    @65
    wb
    vh
    vex
    @26
    @22
    cA
    cO
    cvv
    cY
    elecg
    sylancr
    vx
    vy
    cA
    @22
    c.po
    cO
    vg
    vw
    cX
    cY
    orbsta.o
    gaorb
    syl6bb
    biimpa
    simp3d
    @2
    @62
    @59
    @2
    @61
    @59
    vw
    cX
    @2
    @51
    wa
    #
    @55
    @57
    wceq
    #
    vz
    @3
    wrex
    #
    @61
    @59
    @66
    @45
    @3
    wcel
    #
    @55
    @46
    wceq
    #
    @68
    @51
    @69
    @2
    cX
    @44
    c.sm
    c.sm
    cG
    cH
    cqg
    co
    cvv
    orbsta.r
    cG
    cH
    cqg
    ovex
    eqeltri
    ecelqsi
    adantl
    @66
    @46
    @55
    @56
    eqcomd
    @67
    @70
    vz
    @45
    @3
    @34
    @45
    wceq
    @57
    @46
    @55
    @34
    @45
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @61
    @67
    @58
    vz
    @3
    @55
    @22
    @57
    eqeq1
    rexbidv
    syl5ibcom
    rexlimdva
    imp
    syldan
    ralrimiva
    vz
    vh
    @3
    @4
    cF
    dffo3
    sylanbrc
    @3
    @4
    cF
    df-f1o
    sylanbrc
end
