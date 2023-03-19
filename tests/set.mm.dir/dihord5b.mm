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
include "simpl1.mm"
include "simpl3.mm"
include "eqid.mm"
include "lhpmcvr2.mm"
include "syl2anc.mm"
include "wi.mm"
include "cdib.mm"
include "cdic.mm"
include "cdvh.mm"
include "clsm.mm"
include "simp1r.mm"
include "simpl2r.mm"
include "3ad2ant1.mm"
include "clat.mm"
include "wb.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "dibord.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssssubg.mm"
include "simp2.mm"
include "diclss.mm"
include "sseldd.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmub2.mm"
include "sstrd.mm"
include "dihvalb.mm"
include "simp1l3.mm"
include "simp3.mm"
include "dihvalcq.mm"
include "3sstr4d.mm"
include "3exp.mm"
include "expd.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem dihord5b
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ -. Y .<_ W ) ) /\ X .<_ Y ) -> ( I ` X ) C_ ( I ` Y ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
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
    cX
    cY
    c.le
    wbr
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
    @12
    cY
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
    cY
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
    @11
    @2
    @8
    @20
    @2
    @5
    @8
    @10
    simpl1
    @2
    @5
    @8
    @10
    simpl3
    @19
    cB
    cH
    @16
    cK
    c.le
    @14
    cW
    cY
    vr
    dihord3.b
    dihord3.l
    @16
    eqid
    #
    @14
    eqid
    #
    @19
    eqid
    #
    dihord3.h
    lhpmcvr2
    syl2anc
    @11
    @18
    @23
    vr
    @19
    @11
    @12
    @19
    wcel
    #
    @13
    @17
    @23
    @11
    @27
    @13
    @17
    @23
    wi
    @11
    @27
    @13
    wa
    #
    @17
    @23
    @11
    @28
    @17
    w3a
    #
    cX
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    @12
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    @15
    @30
    cfv
    #
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
    @21
    @22
    @29
    @31
    @34
    @37
    @29
    @31
    @34
    wss
    #
    cX
    @15
    c.le
    wbr
    #
    @29
    @10
    @4
    @39
    @9
    @10
    @28
    @17
    simp1r
    @11
    @28
    @4
    @17
    @3
    @4
    @2
    @8
    @10
    simpl2r
    3ad2ant1
    @29
    cK
    clat
    wcel
    #
    @3
    @6
    cW
    cB
    wcel
    #
    @10
    @4
    wa
    @39
    wb
    @29
    @0
    @40
    @11
    @28
    @0
    @17
    @0
    @1
    @5
    @8
    @10
    simpl1l
    3ad2ant1
    cK
    hllat
    syl
    #
    @11
    @28
    @3
    @17
    @3
    @4
    @2
    @8
    @10
    simpl2l
    3ad2ant1
    @11
    @28
    @6
    @17
    @6
    @7
    @2
    @5
    @10
    simpl3l
    3ad2ant1
    #
    @29
    @1
    @41
    @11
    @28
    @1
    @17
    @0
    @1
    @5
    @8
    @10
    simpl1r
    3ad2ant1
    cB
    cH
    cK
    cW
    dihord3.b
    dihord3.h
    lhpbase
    syl
    #
    cB
    cK
    c.le
    @14
    cX
    cY
    cW
    dihord3.b
    dihord3.l
    @25
    latlem12
    syl13anc
    mpbi2and
    @29
    @2
    @5
    @15
    cB
    wcel
    #
    @15
    cW
    c.le
    wbr
    #
    @38
    @39
    wb
    @2
    @5
    @8
    @10
    @28
    @17
    simp1l1
    #
    @2
    @5
    @8
    @10
    @28
    @17
    simp1l2
    #
    @29
    @40
    @6
    @41
    @45
    @42
    @43
    @44
    cB
    cK
    @14
    cY
    cW
    dihord3.b
    @25
    latmcl
    syl3anc
    #
    @29
    @40
    @6
    @41
    @46
    @42
    @43
    @44
    cB
    cK
    c.le
    @14
    cY
    cW
    dihord3.b
    dihord3.l
    @25
    latmle2
    syl3anc
    #
    cB
    cH
    @30
    cK
    c.le
    cW
    cX
    @15
    dihord3.b
    dihord3.l
    dihord3.h
    @30
    eqid
    #
    dibord
    syl112anc
    mpbird
    @29
    @33
    @35
    csubg
    cfv
    #
    wcel
    @34
    @52
    wcel
    @34
    @37
    wss
    @29
    @35
    clss
    cfv
    #
    @52
    @33
    @29
    @35
    clmod
    wcel
    @53
    @52
    wss
    @29
    @35
    cH
    cK
    cW
    dihord3.h
    @35
    eqid
    #
    @47
    dvhlmod
    @53
    @35
    @53
    eqid
    #
    lsssssubg
    syl
    #
    @29
    @2
    @28
    @33
    @53
    wcel
    @47
    @11
    @28
    @17
    simp2
    #
    @19
    @12
    @53
    @35
    cH
    @32
    cK
    c.le
    cW
    dihord3.l
    @26
    dihord3.h
    @54
    @32
    eqid
    #
    @55
    diclss
    syl2anc
    sseldd
    @29
    @53
    @52
    @34
    @56
    @29
    @2
    @45
    @46
    @34
    @53
    wcel
    @47
    @49
    @50
    cB
    @53
    @35
    cH
    @30
    cK
    c.le
    cW
    @15
    dihord3.b
    dihord3.l
    dihord3.h
    @54
    @51
    @55
    diblss
    syl12anc
    sseldd
    @36
    @33
    @34
    @35
    @36
    eqid
    #
    lsmub2
    syl2anc
    sstrd
    @29
    @2
    @5
    @21
    @31
    wceq
    @47
    @48
    cB
    @30
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dihord3.b
    dihord3.l
    dihord3.h
    dihord3.i
    @51
    dihvalb
    syl2anc
    @29
    @2
    @8
    @28
    @17
    @22
    @37
    wceq
    @47
    @2
    @5
    @8
    @10
    @28
    @17
    simp1l3
    @57
    @11
    @28
    @17
    simp3
    @19
    cB
    @32
    @30
    @36
    @12
    @35
    cH
    cI
    @16
    cK
    c.le
    @14
    cW
    cY
    dihord3.b
    dihord3.l
    @24
    @25
    @26
    dihord3.h
    dihord3.i
    @51
    @58
    @54
    @59
    dihvalcq
    syl112anc
    3sstr4d
    3exp
    expd
    imp4a
    rexlimdv
    mpd
end
