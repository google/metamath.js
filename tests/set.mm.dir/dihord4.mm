include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cmee.mm"
include "cfv.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "catm.mm"
include "wrex.mm"
include "wss.mm"
include "wb.mm"
include "eqid.mm"
include "lhpmcvr2.mm"
include "3adant3.mm"
include "3adant2.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "cdic.mm"
include "cdib.mm"
include "cdvh.mm"
include "clsm.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "jca.mm"
include "simp3lr.mm"
include "dihvalcq.mm"
include "syl112anc.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "sseq12d.mm"
include "simpl11.mm"
include "simpl2l.mm"
include "adantr.mm"
include "simpl2r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simpr.mm"
include "dihord2.mm"
include "syl323anc.mm"
include "dihord1.mm"
include "impbida.mm"
include "bitrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem dihord4
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  assume dihord3.b: |- B = ( Base ` K )
  assume dihord3.l: |- .<_ = ( le ` K )
  assume dihord3.h: |- H = ( LHyp ` K )
  assume dihord3.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ -. Y .<_ W ) ) -> ( ( I ` X ) C_ ( I ` Y ) <-> X .<_ Y ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cB
    wcel
    #
    cY
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @8
    cX
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    cX
    wceq
    #
    wa
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @15
    cY
    cW
    @10
    co
    #
    @12
    co
    cY
    wceq
    #
    wa
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
    @21
    wrex
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    wss
    #
    cX
    cY
    c.le
    wbr
    #
    wb
    #
    @7
    @14
    vq
    @21
    wrex
    #
    @19
    vr
    @21
    wrex
    #
    @22
    @0
    @3
    @28
    @6
    @21
    cB
    cH
    @12
    cK
    c.le
    @10
    cW
    cX
    vq
    dihord3.b
    dihord3.l
    @12
    eqid
    #
    @10
    eqid
    #
    @21
    eqid
    #
    dihord3.h
    lhpmcvr2
    3adant3
    @0
    @6
    @29
    @3
    @21
    cB
    cH
    @12
    cK
    c.le
    @10
    cW
    cY
    vr
    dihord3.b
    dihord3.l
    @30
    @31
    @32
    dihord3.h
    lhpmcvr2
    3adant2
    @14
    @19
    vq
    vr
    @21
    @21
    reeanv
    sylanbrc
    @7
    @20
    @27
    vq
    vr
    @21
    @21
    @7
    @8
    @21
    wcel
    #
    @15
    @21
    wcel
    #
    wa
    #
    @20
    @27
    @7
    @35
    @20
    w3a
    #
    @25
    @8
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    @11
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsm
    cfv
    #
    co
    #
    @15
    @37
    cfv
    @17
    @38
    cfv
    @40
    co
    #
    wss
    #
    @26
    @36
    @23
    @41
    @24
    @42
    @36
    @0
    @3
    @33
    @9
    wa
    #
    @13
    @23
    @41
    wceq
    @0
    @3
    @6
    @35
    @20
    simp11
    #
    @0
    @3
    @6
    @35
    @20
    simp12
    @36
    @33
    @9
    @7
    @33
    @34
    @20
    simp2l
    @9
    @13
    @19
    @7
    @35
    simp3ll
    #
    jca
    @9
    @13
    @19
    @7
    @35
    simp3lr
    #
    @21
    cB
    @37
    @38
    @40
    @8
    @39
    cH
    cI
    @12
    cK
    c.le
    @10
    cW
    cX
    dihord3.b
    dihord3.l
    @30
    @31
    @32
    dihord3.h
    dihord3.i
    @38
    eqid
    #
    @37
    eqid
    #
    @39
    eqid
    #
    @40
    eqid
    #
    dihvalcq
    syl112anc
    @36
    @0
    @6
    @34
    @16
    wa
    #
    @18
    @24
    @42
    wceq
    @45
    @0
    @3
    @6
    @35
    @20
    simp13
    @36
    @34
    @16
    @7
    @33
    @34
    @20
    simp2r
    @16
    @18
    @14
    @7
    @35
    simp3rl
    #
    jca
    @16
    @18
    @14
    @7
    @35
    simp3rr
    #
    @21
    cB
    @37
    @38
    @40
    @15
    @39
    cH
    cI
    @12
    cK
    c.le
    @10
    cW
    cY
    dihord3.b
    dihord3.l
    @30
    @31
    @32
    dihord3.h
    dihord3.i
    @48
    @49
    @50
    @51
    dihvalcq
    syl112anc
    sseq12d
    @36
    @43
    @26
    @36
    @43
    wa
    #
    @0
    @44
    @52
    @1
    @4
    @13
    @18
    @43
    @26
    @0
    @3
    @6
    @35
    @20
    @43
    simpl11
    @55
    @33
    @9
    @33
    @34
    @7
    @20
    @43
    simpl2l
    @36
    @9
    @43
    @46
    adantr
    jca
    @55
    @34
    @16
    @33
    @34
    @7
    @20
    @43
    simpl2r
    @36
    @16
    @43
    @53
    adantr
    jca
    @36
    @1
    @43
    @1
    @2
    @0
    @6
    @35
    @20
    simp12l
    #
    adantr
    @36
    @4
    @43
    @4
    @5
    @0
    @3
    @35
    @20
    simp13l
    #
    adantr
    @36
    @13
    @43
    @47
    adantr
    @36
    @18
    @43
    @54
    adantr
    @36
    @43
    simpr
    @21
    cB
    @40
    @8
    @39
    cH
    @38
    @37
    @12
    cK
    c.le
    @10
    @15
    cW
    cX
    cY
    dihord3.b
    dihord3.l
    @30
    @31
    @32
    dihord3.h
    @48
    @49
    @50
    @51
    dihord2
    syl323anc
    @36
    @26
    wa
    #
    @0
    @44
    @52
    @1
    @4
    @13
    @18
    @26
    @43
    @0
    @3
    @6
    @35
    @20
    @26
    simpl11
    @58
    @33
    @9
    @33
    @34
    @7
    @20
    @26
    simpl2l
    @36
    @9
    @26
    @46
    adantr
    jca
    @58
    @34
    @16
    @33
    @34
    @7
    @20
    @26
    simpl2r
    @36
    @16
    @26
    @53
    adantr
    jca
    @36
    @1
    @26
    @56
    adantr
    @36
    @4
    @26
    @57
    adantr
    @36
    @13
    @26
    @47
    adantr
    @36
    @18
    @26
    @54
    adantr
    @36
    @26
    simpr
    @21
    cB
    @40
    @8
    @15
    @39
    cH
    @38
    @37
    @12
    cK
    c.le
    @10
    cW
    cX
    cY
    dihord3.b
    dihord3.l
    @30
    @31
    @32
    dihord3.h
    @48
    @49
    @50
    @51
    dihord1
    syl323anc
    impbida
    bitrd
    3exp
    rexlimdvv
    mpd
end
