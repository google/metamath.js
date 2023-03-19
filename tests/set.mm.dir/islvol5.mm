include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "clpl.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "islvol3.mm"
include "wex.mm"
include "rexcom4.mm"
include "rexbii.mm"
include "bitri.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "simplll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "atbase.mm"
include "adantl.mm"
include "latjcl.mm"
include "biantrurd.mm"
include "r19.41v.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "an13.mm"
include "exbii.mm"
include "ovex.mm"
include "an12.mm"
include "eleq1.mm"
include "breq2.mm"
include "notbid.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "anass.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "r19.42v.mm"
include "3bitr3g.mm"
include "ceqsexv.mm"
include "syl6rbbr.mm"
include "rexbidva.mm"
include "2rexbidva.mm"
include "syl5rbbr.mm"
include "wb.mm"
include "islpln2.mm"
include "adantr.mm"
include "anbi1d.mm"
include "an32.mm"
include "3bitr4ri.mm"
include "rexcom.mm"
include "exbidv.mm"
include "bitrd.mm"
include "df-rex.mm"

theorem islvol5
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vy: setvar y
  assume islvol5.b: |- B = ( Base ` K )
  assume islvol5.l: |- .<_ = ( le ` K )
  assume islvol5.j: |- .\/ = ( join ` K )
  assume islvol5.a: |- A = ( Atoms ` K )
  assume islvol5.v: |- V = ( LVols ` K )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B s
  disjoint .\/ p
  disjoint .\/ q
  disjoint .\/ r
  disjoint .\/ s
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint .<_ p
  disjoint .<_ q
  disjoint .<_ r
  disjoint .<_ s
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X s
  disjoint p y
  disjoint q y
  disjoint r y
  disjoint s y
  disjoint A y
  disjoint B y
  disjoint .\/ y
  disjoint K y
  disjoint .<_ y
  disjoint X y
  assert |- ( ( K e. HL /\ X e. B ) -> ( X e. V <-> E. p e. A E. q e. A E. r e. A E. s e. A ( ( p =/= q /\ -. r .<_ ( p .\/ q ) /\ -. s .<_ ( ( p .\/ q ) .\/ r ) ) /\ X = ( ( ( p .\/ q ) .\/ r ) .\/ s ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cV
    wcel
    vs
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    wn
    #
    cX
    @4
    @3
    c.or
    co
    #
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    #
    vy
    cK
    clpl
    cfv
    #
    wrex
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    vr
    cv
    #
    @13
    @14
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @3
    @17
    @16
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    cX
    @19
    @3
    c.or
    co
    #
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    #
    vy
    cA
    cB
    @11
    c.or
    cK
    c.le
    cV
    cX
    vs
    islvol5.b
    islvol5.l
    islvol5.j
    islvol5.a
    @11
    eqid
    #
    islvol5.v
    islvol3
    @2
    @28
    @4
    @11
    wcel
    #
    @10
    wa
    #
    vy
    wex
    #
    @12
    @2
    @28
    @4
    cB
    wcel
    #
    @9
    wa
    #
    @15
    @18
    @4
    @19
    wceq
    #
    w3a
    #
    wa
    #
    vs
    cA
    wrex
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    vy
    wex
    #
    @32
    @42
    @38
    vy
    wex
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    @2
    @28
    @46
    @40
    vy
    wex
    #
    vp
    cA
    wrex
    @42
    @45
    @47
    vp
    cA
    @45
    @39
    vy
    wex
    #
    vq
    cA
    wrex
    @47
    @44
    @48
    vq
    cA
    @38
    vr
    vy
    cA
    rexcom4
    rexbii
    @39
    vq
    vy
    cA
    rexcom4
    bitri
    rexbii
    @40
    vp
    vy
    cA
    rexcom4
    bitri
    @2
    @44
    @27
    vp
    vq
    cA
    cA
    @2
    @13
    cA
    wcel
    #
    @14
    cA
    wcel
    #
    wa
    #
    wa
    #
    @43
    @26
    vr
    cA
    @52
    @16
    cA
    wcel
    #
    wa
    #
    @26
    @19
    cB
    wcel
    #
    @26
    wa
    #
    @43
    @54
    @55
    @26
    @54
    cK
    clat
    wcel
    #
    @17
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @55
    @0
    @57
    @1
    @51
    @53
    cK
    hllat
    ad3antrrr
    @54
    @0
    @49
    @50
    @58
    @0
    @1
    @51
    @53
    simplll
    @2
    @49
    @50
    @53
    simplrl
    @2
    @49
    @50
    @53
    simplrr
    cA
    cB
    c.or
    cK
    @13
    @14
    islvol5.b
    islvol5.j
    islvol5.a
    hlatjcl
    syl3anc
    @53
    @59
    @52
    cA
    cB
    @16
    cK
    islvol5.b
    islvol5.a
    atbase
    adantl
    cB
    c.or
    cK
    @17
    @16
    islvol5.b
    islvol5.j
    latjcl
    syl3anc
    biantrurd
    @43
    @35
    @15
    @18
    wa
    #
    @34
    vs
    cA
    wrex
    #
    wa
    #
    wa
    #
    vy
    wex
    @56
    @38
    @63
    vy
    @38
    @61
    @36
    wa
    #
    @63
    @34
    @36
    vs
    cA
    r19.41v
    @64
    @61
    @60
    @35
    wa
    #
    wa
    @63
    @36
    @65
    @61
    @15
    @18
    @35
    df-3an
    anbi2i
    @61
    @60
    @35
    an13
    bitri
    bitri
    exbii
    @62
    @56
    vy
    @19
    @17
    @16
    c.or
    ovex
    @35
    @60
    @34
    wa
    #
    vs
    cA
    wrex
    @55
    @25
    wa
    #
    vs
    cA
    wrex
    @62
    @56
    @35
    @66
    @67
    vs
    cA
    @66
    @33
    @60
    @9
    wa
    #
    wa
    @35
    @67
    @60
    @33
    @9
    an12
    @35
    @33
    @55
    @68
    @25
    @4
    @19
    cB
    eleq1
    @35
    @68
    @60
    @21
    @24
    wa
    #
    wa
    #
    @25
    @35
    @9
    @69
    @60
    @35
    @6
    @21
    @8
    @24
    @35
    @5
    @20
    @4
    @19
    @3
    c.le
    breq2
    notbid
    @35
    @7
    @23
    cX
    @4
    @19
    @3
    c.or
    oveq1
    eqeq2d
    anbi12d
    anbi2d
    @70
    @60
    @21
    wa
    #
    @24
    wa
    @25
    @60
    @21
    @24
    anass
    @71
    @22
    @24
    @22
    @71
    @15
    @18
    @21
    df-3an
    bicomi
    anbi1i
    bitr3i
    syl6bb
    anbi12d
    syl5bb
    rexbidv
    @60
    @34
    vs
    cA
    r19.42v
    @55
    @25
    vs
    cA
    r19.42v
    3bitr3g
    ceqsexv
    bitri
    syl6rbbr
    rexbidva
    2rexbidva
    syl5rbbr
    @2
    @41
    @31
    vy
    @2
    @41
    @30
    @9
    wa
    #
    vs
    cA
    wrex
    #
    @31
    @2
    @73
    @37
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    vs
    cA
    wrex
    #
    @41
    @2
    @72
    @76
    vs
    cA
    @2
    @72
    @33
    @36
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    wa
    #
    @9
    wa
    #
    @76
    @2
    @30
    @81
    @9
    @0
    @30
    @81
    wb
    @1
    cA
    cB
    @11
    c.or
    cK
    c.le
    @4
    vr
    vq
    vp
    islvol5.b
    islvol5.l
    islvol5.j
    islvol5.a
    @29
    islpln2
    adantr
    anbi1d
    @34
    @79
    wa
    #
    vp
    cA
    wrex
    @34
    @80
    wa
    @76
    @82
    @34
    @79
    vp
    cA
    r19.42v
    @75
    @83
    vp
    cA
    @75
    @34
    @78
    wa
    #
    vq
    cA
    wrex
    @83
    @74
    @84
    vq
    cA
    @34
    @36
    vr
    cA
    r19.42v
    rexbii
    @34
    @78
    vq
    cA
    r19.42v
    bitri
    rexbii
    @33
    @80
    @9
    an32
    3bitr4ri
    syl6bb
    rexbidv
    @41
    @75
    vs
    cA
    wrex
    #
    vp
    cA
    wrex
    @77
    @40
    @85
    vp
    cA
    @40
    @74
    vs
    cA
    wrex
    #
    vq
    cA
    wrex
    @85
    @39
    @86
    vq
    cA
    @37
    vr
    vs
    cA
    cA
    rexcom
    rexbii
    @74
    vq
    vs
    cA
    cA
    rexcom
    bitri
    rexbii
    @75
    vp
    vs
    cA
    cA
    rexcom
    bitri
    syl6rbbr
    @30
    @9
    vs
    cA
    r19.42v
    syl6bb
    exbidv
    bitrd
    @10
    vy
    @11
    df-rex
    syl6rbbr
    bitrd
end
