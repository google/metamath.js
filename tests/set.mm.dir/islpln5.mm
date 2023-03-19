include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "clln.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "islpln3.mm"
include "wex.mm"
include "rexcom4.mm"
include "rexbii.mm"
include "bitri.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "biantrurd.mm"
include "r19.41v.mm"
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
include "3anass.mm"
include "syl6bbr.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "r19.42v.mm"
include "3bitr3g.mm"
include "ceqsexv.mm"
include "syl6rbbr.mm"
include "2rexbidva.mm"
include "syl5rbbr.mm"
include "wb.mm"
include "islln2.mm"
include "adantr.mm"
include "anbi1d.mm"
include "an32.mm"
include "3bitr4ri.mm"
include "syl6bb.mm"
include "rexcom.mm"
include "exbidv.mm"
include "bitrd.mm"
include "df-rex.mm"

theorem islpln5
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vy: setvar y
  assume islpln5.b: |- B = ( Base ` K )
  assume islpln5.l: |- .<_ = ( le ` K )
  assume islpln5.j: |- .\/ = ( join ` K )
  assume islpln5.a: |- A = ( Atoms ` K )
  assume islpln5.p: |- P = ( LPlanes ` K )

  disjoint p q
  disjoint p r
  disjoint A p
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint .\/ p
  disjoint .\/ q
  disjoint .\/ r
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint .<_ p
  disjoint .<_ q
  disjoint .<_ r
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint p y
  disjoint q y
  disjoint r y
  disjoint A y
  disjoint B y
  disjoint .\/ y
  disjoint K y
  disjoint .<_ y
  disjoint X y
  assert |- ( ( K e. HL /\ X e. B ) -> ( X e. P <-> E. p e. A E. q e. A E. r e. A ( p =/= q /\ -. r .<_ ( p .\/ q ) /\ X = ( ( p .\/ q ) .\/ r ) ) ) )

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
    cP
    wcel
    vr
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
    vr
    cA
    wrex
    #
    vy
    cK
    clln
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
    @3
    @13
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cX
    @16
    @3
    c.or
    co
    #
    wceq
    #
    w3a
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
    cP
    c.or
    cK
    c.le
    @11
    cX
    vr
    islpln5.b
    islpln5.l
    islpln5.j
    islpln5.a
    @11
    eqid
    #
    islpln5.p
    islpln3
    @2
    @23
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
    @23
    @4
    cB
    wcel
    #
    @9
    wa
    #
    @15
    @4
    @16
    wceq
    #
    wa
    #
    wa
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
    @27
    @36
    @33
    vy
    wex
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
    @23
    @39
    @34
    vy
    wex
    #
    vp
    cA
    wrex
    @36
    @38
    @40
    vp
    cA
    @33
    vq
    vy
    cA
    rexcom4
    rexbii
    @34
    vp
    vy
    cA
    rexcom4
    bitri
    @2
    @37
    @22
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
    @22
    @16
    cB
    wcel
    #
    @22
    wa
    #
    @37
    @44
    @45
    @22
    @44
    @0
    @41
    @42
    @45
    @0
    @1
    @43
    simpll
    @2
    @41
    @42
    simprl
    @2
    @41
    @42
    simprr
    cA
    cB
    c.or
    cK
    @13
    @14
    islpln5.b
    islpln5.j
    islpln5.a
    hlatjcl
    syl3anc
    biantrurd
    @37
    @30
    @15
    @29
    vr
    cA
    wrex
    #
    wa
    #
    wa
    #
    vy
    wex
    @46
    @33
    @49
    vy
    @33
    @47
    @31
    wa
    @49
    @29
    @31
    vr
    cA
    r19.41v
    @47
    @15
    @30
    an13
    bitri
    exbii
    @48
    @46
    vy
    @16
    @13
    @14
    c.or
    ovex
    @30
    @15
    @29
    wa
    #
    vr
    cA
    wrex
    @45
    @21
    wa
    #
    vr
    cA
    wrex
    @48
    @46
    @30
    @50
    @51
    vr
    cA
    @50
    @28
    @15
    @9
    wa
    #
    wa
    @30
    @51
    @15
    @28
    @9
    an12
    @30
    @28
    @45
    @52
    @21
    @4
    @16
    cB
    eleq1
    @30
    @52
    @15
    @18
    @20
    wa
    #
    wa
    @21
    @30
    @9
    @53
    @15
    @30
    @6
    @18
    @8
    @20
    @30
    @5
    @17
    @4
    @16
    @3
    c.le
    breq2
    notbid
    @30
    @7
    @19
    cX
    @4
    @16
    @3
    c.or
    oveq1
    eqeq2d
    anbi12d
    anbi2d
    @15
    @18
    @20
    3anass
    syl6bbr
    anbi12d
    syl5bb
    rexbidv
    @15
    @29
    vr
    cA
    r19.42v
    @45
    @21
    vr
    cA
    r19.42v
    3bitr3g
    ceqsexv
    bitri
    syl6rbbr
    2rexbidva
    syl5rbbr
    @2
    @35
    @26
    vy
    @2
    @35
    @25
    @9
    wa
    #
    vr
    cA
    wrex
    #
    @26
    @2
    @55
    @32
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    vr
    cA
    wrex
    #
    @35
    @2
    @54
    @57
    vr
    cA
    @2
    @54
    @28
    @31
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
    @57
    @2
    @25
    @61
    @9
    @0
    @25
    @61
    wb
    @1
    cA
    cB
    c.or
    cK
    @11
    @4
    vq
    vp
    islpln5.b
    islpln5.j
    islpln5.a
    @24
    islln2
    adantr
    anbi1d
    @29
    @59
    wa
    #
    vp
    cA
    wrex
    @29
    @60
    wa
    @57
    @62
    @29
    @59
    vp
    cA
    r19.42v
    @56
    @63
    vp
    cA
    @29
    @31
    vq
    cA
    r19.42v
    rexbii
    @28
    @60
    @9
    an32
    3bitr4ri
    syl6bb
    rexbidv
    @35
    @56
    vr
    cA
    wrex
    #
    vp
    cA
    wrex
    @58
    @34
    @64
    vp
    cA
    @32
    vq
    vr
    cA
    cA
    rexcom
    rexbii
    @56
    vp
    vr
    cA
    cA
    rexcom
    bitri
    syl6rbbr
    @25
    @9
    vr
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
