include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wn.mm"
include "wceq.mm"
include "catm.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "islpln2.mm"
include "simpr.mm"
include "syl6bi.mm"
include "anim12d.mm"
include "imp.mm"
include "3adantr3.mm"
include "3adant3.mm"
include "wi.mm"
include "simpl33.mm"
include "3ad2ant1.mm"
include "simp33.mm"
include "oveq12d.mm"
include "simp11.mm"
include "simp123.mm"
include "jca.mm"
include "adantr.mm"
include "simp2l.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "3jca.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simp1r.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp32.mm"
include "simpl13.mm"
include "wb.mm"
include "breq1.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "neeq2.mm"
include "3anbi23d.mm"
include "sylan9bb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "2lplnja.mm"
include "syl321anc.mm"
include "eqtrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "rexlimdva.mm"
include "expdimp.mm"
include "impd.mm"
include "mpd.mm"

theorem 2lplnj
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume 2lplnj.l: |- .<_ = ( le ` K )
  assume 2lplnj.j: |- .\/ = ( join ` K )
  assume 2lplnj.p: |- P = ( LPlanes ` K )
  assume 2lplnj.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ ( X e. P /\ Y e. P /\ W e. V ) /\ ( X .<_ W /\ Y .<_ W /\ X =/= Y ) ) -> ( X .\/ Y ) = W )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    cW
    cV
    wcel
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    #
    cY
    cW
    c.le
    wbr
    #
    cX
    cY
    wne
    #
    w3a
    #
    w3a
    #
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    vs
    cv
    #
    @10
    @11
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cX
    @14
    @13
    c.or
    co
    #
    wceq
    #
    w3a
    #
    vs
    cK
    catm
    cfv
    #
    wrex
    vr
    @19
    wrex
    #
    vq
    @19
    wrex
    #
    vt
    cv
    #
    vu
    cv
    #
    wne
    #
    vv
    cv
    #
    @22
    @23
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cY
    @26
    @25
    c.or
    co
    #
    wceq
    #
    w3a
    #
    vv
    @19
    wrex
    vu
    @19
    wrex
    #
    vt
    @19
    wrex
    #
    wa
    #
    cX
    cY
    c.or
    co
    #
    cW
    wceq
    #
    @0
    @4
    @33
    @8
    @0
    @1
    @2
    @33
    @3
    @0
    @1
    @2
    wa
    @33
    @0
    @1
    @21
    @2
    @32
    @0
    @1
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @21
    wa
    @21
    @19
    @36
    cP
    c.or
    cK
    c.le
    cX
    vs
    vr
    vq
    @36
    eqid
    #
    2lplnj.l
    2lplnj.j
    @19
    eqid
    #
    2lplnj.p
    islpln2
    @37
    @21
    simpr
    syl6bi
    @0
    @2
    cY
    @36
    wcel
    #
    @32
    wa
    @32
    @19
    @36
    cP
    c.or
    cK
    c.le
    cY
    vv
    vu
    vt
    @38
    2lplnj.l
    2lplnj.j
    @39
    2lplnj.p
    islpln2
    @40
    @32
    simpr
    syl6bi
    anim12d
    imp
    3adantr3
    3adant3
    @9
    @21
    @32
    @35
    @9
    @20
    @32
    @35
    wi
    #
    vq
    @19
    @9
    @10
    @19
    wcel
    #
    wa
    @18
    @41
    vr
    vs
    @19
    @19
    @9
    @42
    @11
    @19
    wcel
    #
    @13
    @19
    wcel
    #
    wa
    #
    @18
    @41
    wi
    @9
    @42
    @45
    wa
    #
    @18
    @41
    @9
    @46
    @18
    w3a
    #
    @31
    @35
    vt
    @19
    @47
    @22
    @19
    wcel
    #
    wa
    #
    @30
    @35
    vu
    vv
    @19
    @19
    @49
    @23
    @19
    wcel
    #
    @25
    @19
    wcel
    #
    wa
    #
    @30
    @35
    @49
    @52
    @30
    w3a
    #
    @34
    @16
    @28
    c.or
    co
    #
    cW
    @53
    cX
    @16
    cY
    @28
    c.or
    @49
    @52
    @17
    @30
    @12
    @15
    @17
    @9
    @46
    @48
    simpl33
    3ad2ant1
    #
    @49
    @52
    @24
    @27
    @29
    simp33
    #
    oveq12d
    @53
    @0
    @3
    wa
    #
    @42
    @43
    @44
    w3a
    #
    @12
    @15
    wa
    @48
    @50
    @51
    w3a
    @24
    @27
    wa
    @16
    cW
    c.le
    wbr
    #
    @28
    cW
    c.le
    wbr
    #
    @16
    @28
    wne
    #
    w3a
    #
    @54
    cW
    wceq
    @49
    @52
    @57
    @30
    @47
    @57
    @48
    @47
    @0
    @3
    @0
    @4
    @8
    @46
    @18
    simp11
    @1
    @2
    @3
    @0
    @8
    @46
    @18
    simp123
    jca
    adantr
    3ad2ant1
    @49
    @52
    @58
    @30
    @47
    @58
    @48
    @47
    @42
    @43
    @44
    @9
    @42
    @45
    @18
    simp2l
    @43
    @44
    @42
    @9
    @18
    simp2rl
    @43
    @44
    @42
    @9
    @18
    simp2rr
    3jca
    adantr
    3ad2ant1
    @53
    @12
    @15
    @49
    @52
    @12
    @30
    @12
    @15
    @17
    @9
    @46
    @48
    simpl31
    3ad2ant1
    @49
    @52
    @15
    @30
    @12
    @15
    @17
    @9
    @46
    @48
    simpl32
    3ad2ant1
    jca
    @53
    @48
    @50
    @51
    @47
    @48
    @52
    @30
    simp1r
    @49
    @50
    @51
    @30
    simp2l
    @49
    @50
    @51
    @30
    simp2r
    3jca
    @53
    @24
    @27
    @49
    @52
    @24
    @27
    @29
    simp31
    @49
    @52
    @24
    @27
    @29
    simp32
    jca
    @53
    @8
    @62
    @49
    @52
    @8
    @30
    @0
    @4
    @8
    @46
    @18
    @48
    simpl13
    3ad2ant1
    @53
    @17
    @29
    @8
    @62
    wb
    @55
    @56
    @17
    @8
    @59
    @6
    @16
    cY
    wne
    #
    w3a
    @29
    @62
    @17
    @5
    @59
    @7
    @63
    @6
    cX
    @16
    cW
    c.le
    breq1
    cX
    @16
    cY
    neeq1
    3anbi13d
    @29
    @6
    @60
    @63
    @61
    @59
    cY
    @28
    cW
    c.le
    breq1
    cY
    @28
    @16
    neeq2
    3anbi23d
    sylan9bb
    syl2anc
    mpbid
    @19
    @10
    @11
    @13
    @22
    @23
    @25
    c.or
    cK
    c.le
    cV
    cW
    2lplnj.l
    2lplnj.j
    @39
    2lplnj.v
    2lplnja
    syl321anc
    eqtrd
    3exp
    rexlimdvv
    rexlimdva
    3exp
    expdimp
    rexlimdvv
    rexlimdva
    impd
    mpd
end
