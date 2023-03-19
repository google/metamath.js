include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wrel.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "relopabi.mm"
include "a1i.mm"
include "wbr.mm"
include "w3a.mm"
include "simpr.mm"
include "gaorb.mm"
include "sylib.mm"
include "simp2d.mm"
include "simp1d.mm"
include "simp3d.mm"
include "cminusg.mm"
include "cfv.mm"
include "wb.mm"
include "simpll.mm"
include "adantr.mm"
include "eqid.mm"
include "gacan.mm"
include "syl13anc.mm"
include "wi.mm"
include "cgrp.mm"
include "gagrp.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "syl.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "syl3anbrc.mm"
include "adantrr.mm"
include "simprr.mm"
include "reeanv.mm"
include "cplusg.mm"
include "ad2antrr.mm"
include "simprlr.mm"
include "simprll.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "gaass.mm"
include "simprrl.mm"
include "oveq2d.mm"
include "simprrr.mm"
include "3eqtrd.mm"
include "syl2anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "c0g.mm"
include "grpidcl.mm"
include "gagrpid.mm"
include "pm4.71rd.mm"
include "df-3an.mm"
include "anidm.mm"
include "anbi2ci.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "iserd.mm"

theorem gaorber
  let vx: setvar x
  let vy: setvar y
  let c.po: class .(+)
  let c.sm: class .~
  let vg: setvar g
  let cG: class G
  let cX: class X
  let cY: class Y
  let vh: setvar h
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume gaorb.1: |- .~ = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }
  assume gaorber.2: |- X = ( Base ` G )

  disjoint g x
  disjoint g y
  disjoint x y
  disjoint .(+) g
  disjoint .(+) x
  disjoint .(+) y
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint g h
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint B g
  disjoint B h
  disjoint B x
  disjoint B y
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
  disjoint .~ h
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
  disjoint .(+) h
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
  disjoint X h
  disjoint X k
  disjoint Y f
  disjoint Y h
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  assert |- ( .(+) e. ( G GrpAct Y ) -> .~ Er Y )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    vu
    vv
    vw
    cY
    c.sm
    c.sm
    wrel
    @0
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cY
    wss
    vg
    cv
    @1
    c.po
    co
    @2
    wceq
    vg
    cX
    wrex
    wa
    vx
    vy
    c.sm
    gaorb.1
    relopabi
    a1i
    @0
    vu
    cv
    #
    vv
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    @4
    cY
    wcel
    #
    @3
    cY
    wcel
    #
    vk
    cv
    #
    @4
    c.po
    co
    #
    @3
    wceq
    #
    vk
    cX
    wrex
    #
    @4
    @3
    c.sm
    wbr
    @6
    @8
    @7
    vh
    cv
    #
    @3
    c.po
    co
    #
    @4
    wceq
    #
    vh
    cX
    wrex
    #
    @6
    @5
    @8
    @7
    @16
    w3a
    @0
    @5
    simpr
    vx
    vy
    @3
    @4
    c.po
    c.sm
    vg
    vh
    cX
    cY
    gaorb.1
    gaorb
    sylib
    #
    simp2d
    #
    @6
    @8
    @7
    @16
    @17
    simp1d
    #
    @6
    @16
    @12
    @6
    @8
    @7
    @16
    @17
    simp3d
    #
    @6
    @15
    @12
    vh
    cX
    @6
    @13
    cX
    wcel
    #
    wa
    #
    @15
    @13
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    c.po
    co
    #
    @3
    wceq
    #
    @12
    @22
    @0
    @21
    @8
    @7
    @15
    @26
    wb
    @0
    @5
    @21
    simpll
    @6
    @21
    simpr
    @6
    @8
    @21
    @19
    adantr
    @6
    @7
    @21
    @18
    adantr
    @13
    @3
    @4
    c.po
    cG
    @23
    cX
    cY
    gaorber.2
    @23
    eqid
    #
    gacan
    syl13anc
    @22
    @24
    cX
    wcel
    #
    @26
    @12
    wi
    @6
    cG
    cgrp
    wcel
    #
    @21
    @28
    @0
    @29
    @5
    c.po
    cG
    cY
    gagrp
    #
    adantr
    cX
    cG
    @23
    @13
    gaorber.2
    @27
    grpinvcl
    sylan
    @28
    @26
    @12
    @11
    @26
    vk
    @24
    cX
    @9
    @24
    wceq
    @10
    @25
    @3
    @9
    @24
    @4
    c.po
    oveq1
    eqeq1d
    rspcev
    ex
    syl
    sylbid
    rexlimdva
    mpd
    vx
    vy
    @4
    @3
    c.po
    c.sm
    vg
    vk
    cX
    cY
    gaorb.1
    gaorb
    syl3anbrc
    @0
    @5
    @4
    vw
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    wa
    #
    @8
    @31
    cY
    wcel
    #
    vf
    cv
    #
    @3
    c.po
    co
    #
    @31
    wceq
    #
    vf
    cX
    wrex
    #
    @3
    @31
    c.sm
    wbr
    @0
    @5
    @8
    @32
    @19
    adantrr
    #
    @34
    @7
    @35
    @10
    @31
    wceq
    #
    vk
    cX
    wrex
    #
    @34
    @32
    @7
    @35
    @42
    w3a
    @0
    @5
    @32
    simprr
    vx
    vy
    @4
    @31
    c.po
    c.sm
    vg
    vk
    cX
    cY
    gaorb.1
    gaorb
    sylib
    #
    simp2d
    @34
    @16
    @42
    @39
    @0
    @5
    @16
    @32
    @20
    adantrr
    @34
    @7
    @35
    @42
    @43
    simp3d
    @16
    @42
    wa
    @15
    @41
    wa
    #
    vk
    cX
    wrex
    vh
    cX
    wrex
    @34
    @39
    @15
    @41
    vh
    vk
    cX
    cX
    reeanv
    @34
    @44
    @39
    vh
    vk
    cX
    cX
    @34
    @21
    @9
    cX
    wcel
    #
    wa
    #
    @44
    @39
    @34
    @46
    @44
    wa
    #
    wa
    #
    @9
    @13
    cG
    cplusg
    cfv
    #
    co
    #
    cX
    wcel
    #
    @50
    @3
    c.po
    co
    #
    @31
    wceq
    #
    @39
    @48
    @29
    @45
    @21
    @51
    @0
    @29
    @33
    @47
    @30
    ad2antrr
    @34
    @21
    @45
    @44
    simprlr
    #
    @34
    @21
    @45
    @44
    simprll
    #
    cX
    @49
    cG
    @9
    @13
    gaorber.2
    @49
    eqid
    #
    grpcl
    syl3anc
    @48
    @52
    @9
    @14
    c.po
    co
    #
    @10
    @31
    @48
    @0
    @45
    @21
    @8
    @52
    @57
    wceq
    @0
    @33
    @47
    simpll
    @54
    @55
    @34
    @8
    @47
    @40
    adantr
    @9
    @13
    @3
    @49
    c.po
    cG
    cX
    cY
    gaorber.2
    @56
    gaass
    syl13anc
    @48
    @14
    @4
    @9
    c.po
    @34
    @46
    @15
    @41
    simprrl
    oveq2d
    @34
    @46
    @15
    @41
    simprrr
    3eqtrd
    @38
    @53
    vf
    @50
    cX
    @36
    @50
    wceq
    @37
    @52
    @31
    @36
    @50
    @3
    c.po
    oveq1
    eqeq1d
    rspcev
    syl2anc
    expr
    rexlimdvva
    syl5bir
    mp2and
    vx
    vy
    @3
    @31
    c.po
    c.sm
    vg
    vf
    cX
    cY
    gaorb.1
    gaorb
    syl3anbrc
    @0
    @8
    @8
    @8
    @14
    @3
    wceq
    #
    vh
    cX
    wrex
    #
    w3a
    #
    @3
    @3
    c.sm
    wbr
    @0
    @8
    @59
    @8
    wa
    #
    @60
    @0
    @8
    @59
    @0
    @8
    @59
    @0
    @8
    wa
    #
    cG
    c0g
    cfv
    #
    cX
    wcel
    #
    @63
    @3
    c.po
    co
    #
    @3
    wceq
    #
    @59
    @62
    @29
    @64
    @0
    @29
    @8
    @30
    adantr
    cX
    cG
    @63
    gaorber.2
    @63
    eqid
    #
    grpidcl
    syl
    @3
    c.po
    cG
    cY
    @63
    @67
    gagrpid
    @58
    @66
    vh
    @63
    cX
    @13
    @63
    wceq
    @14
    @65
    @3
    @13
    @63
    @3
    c.po
    oveq1
    eqeq1d
    rspcev
    syl2anc
    ex
    pm4.71rd
    @60
    @8
    @8
    wa
    #
    @59
    wa
    @61
    @8
    @8
    @59
    df-3an
    @68
    @8
    @59
    @8
    anidm
    anbi2ci
    bitri
    syl6bbr
    vx
    vy
    @3
    @3
    c.po
    c.sm
    vg
    vh
    cX
    cY
    gaorb.1
    gaorb
    syl6bbr
    iserd
end
