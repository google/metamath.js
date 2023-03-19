include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "catm.mm"
include "cfv.mm"
include "wrex.mm"
include "cbs.mm"
include "eqid.mm"
include "islln2.mm"
include "simpr.mm"
include "syl6bi.mm"
include "anim12d.mm"
include "imp.mm"
include "3adantr3.mm"
include "3adant3.mm"
include "wi.mm"
include "simp2rr.mm"
include "simp3rr.mm"
include "oveq12d.mm"
include "simp13.mm"
include "wb.mm"
include "breq1.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "neeq2.mm"
include "3anbi23d.mm"
include "sylan9bb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp11.mm"
include "simp123.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp2rl.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "simp3rl.mm"
include "2llnjaN.mm"
include "ex.mm"
include "syl233anc.mm"
include "mpd.mm"
include "eqtrd.mm"
include "3exp.mm"
include "3impib.mm"
include "expd.mm"
include "rexlimdvv.mm"
include "impd.mm"

theorem 2llnjN
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  assume 2llnj.l: |- .<_ = ( le ` K )
  assume 2llnj.j: |- .\/ = ( join ` K )
  assume 2llnj.n: |- N = ( LLines ` K )
  assume 2llnj.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ ( X e. N /\ Y e. N /\ W e. P ) /\ ( X .<_ W /\ Y .<_ W /\ X =/= Y ) ) -> ( X .\/ Y ) = W )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    cW
    cP
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
    cX
    @10
    @11
    c.or
    co
    #
    wceq
    #
    wa
    #
    vr
    cK
    catm
    cfv
    #
    wrex
    vq
    @16
    wrex
    #
    vs
    cv
    #
    vt
    cv
    #
    wne
    #
    cY
    @18
    @19
    c.or
    co
    #
    wceq
    #
    wa
    #
    vt
    @16
    wrex
    vs
    @16
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
    @25
    @8
    @0
    @1
    @2
    @25
    @3
    @0
    @1
    @2
    wa
    @25
    @0
    @1
    @17
    @2
    @24
    @0
    @1
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    wa
    @17
    @16
    @28
    c.or
    cK
    cN
    cX
    vr
    vq
    @28
    eqid
    #
    2llnj.j
    @16
    eqid
    #
    2llnj.n
    islln2
    @29
    @17
    simpr
    syl6bi
    @0
    @2
    cY
    @28
    wcel
    #
    @24
    wa
    @24
    @16
    @28
    c.or
    cK
    cN
    cY
    vt
    vs
    @30
    2llnj.j
    @31
    2llnj.n
    islln2
    @32
    @24
    simpr
    syl6bi
    anim12d
    imp
    3adantr3
    3adant3
    @9
    @17
    @24
    @27
    @9
    @15
    @24
    @27
    wi
    #
    vq
    vr
    @16
    @16
    @9
    @10
    @16
    wcel
    #
    @11
    @16
    wcel
    #
    wa
    #
    @15
    @33
    @9
    @36
    @15
    w3a
    #
    @23
    @27
    vs
    vt
    @16
    @16
    @37
    @18
    @16
    wcel
    #
    @19
    @16
    wcel
    #
    wa
    #
    @23
    @27
    @9
    @36
    @15
    @40
    @23
    wa
    #
    @27
    wi
    @9
    @36
    @15
    wa
    #
    @41
    @27
    @9
    @42
    @41
    w3a
    #
    @26
    @13
    @21
    c.or
    co
    #
    cW
    @43
    cX
    @13
    cY
    @21
    c.or
    @12
    @14
    @36
    @9
    @41
    simp2rr
    #
    @20
    @22
    @40
    @9
    @42
    simp3rr
    #
    oveq12d
    @43
    @13
    cW
    c.le
    wbr
    #
    @21
    cW
    c.le
    wbr
    #
    @13
    @21
    wne
    #
    w3a
    #
    @44
    cW
    wceq
    #
    @43
    @8
    @50
    @0
    @4
    @8
    @42
    @41
    simp13
    @43
    @14
    @22
    @8
    @50
    wb
    @45
    @46
    @14
    @8
    @47
    @6
    @13
    cY
    wne
    #
    w3a
    @22
    @50
    @14
    @5
    @47
    @7
    @52
    @6
    cX
    @13
    cW
    c.le
    breq1
    cX
    @13
    cY
    neeq1
    3anbi13d
    @22
    @6
    @48
    @52
    @49
    @47
    cY
    @21
    cW
    c.le
    breq1
    cY
    @21
    @13
    neeq2
    3anbi23d
    sylan9bb
    syl2anc
    mpbid
    @43
    @0
    @3
    @34
    @35
    @12
    @38
    @39
    @20
    @50
    @51
    wi
    @0
    @4
    @8
    @42
    @41
    simp11
    @1
    @2
    @3
    @0
    @8
    @42
    @41
    simp123
    @34
    @35
    @15
    @9
    @41
    simp2ll
    @34
    @35
    @15
    @9
    @41
    simp2lr
    @12
    @14
    @36
    @9
    @41
    simp2rl
    @38
    @39
    @23
    @9
    @42
    simp3ll
    @38
    @39
    @23
    @9
    @42
    simp3lr
    @20
    @22
    @40
    @9
    @42
    simp3rl
    @0
    @3
    wa
    @34
    @35
    @12
    w3a
    @38
    @39
    @20
    w3a
    w3a
    @50
    @51
    @16
    cP
    @10
    @11
    @18
    @19
    c.or
    cK
    c.le
    cN
    cW
    2llnj.l
    2llnj.j
    @31
    2llnj.n
    2llnj.p
    2llnjaN
    ex
    syl233anc
    mpd
    eqtrd
    3exp
    3impib
    expd
    rexlimdvv
    3exp
    rexlimdvv
    impd
    mpd
end
