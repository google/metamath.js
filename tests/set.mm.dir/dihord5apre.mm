include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl3.mm"
include "lhpmcvr2.mm"
include "syl2anc.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp3ll.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp13l.mm"
include "latlej2.mm"
include "cdic.mm"
include "cdib.mm"
include "simp11.mm"
include "simp3lr.mm"
include "latlej1.mm"
include "wi.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "simp3l.mm"
include "simp12.mm"
include "lhple.mm"
include "oveq2d.mm"
include "eqid.mm"
include "dihvalcq.mm"
include "syl122anc.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssssubg.mm"
include "diclss.mm"
include "sseldd.mm"
include "latmcl.mm"
include "latmle2.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmub1.mm"
include "simp13.mm"
include "simp3r.mm"
include "syl112anc.mm"
include "sseqtr4d.mm"
include "fveq2d.mm"
include "dihvalb.mm"
include "eqtr4d.mm"
include "simp2.mm"
include "eqsstrd.mm"
include "wb.mm"
include "dihlss.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "dihord4.mm"
include "syl121anc.mm"
include "mpbid.mm"
include "lattrd.mm"
include "3expia.mm"
include "exp4c.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem dihord5apre
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  assume dihord5apre.b: |- B = ( Base ` K )
  assume dihord5apre.l: |- .<_ = ( le ` K )
  assume dihord5apre.h: |- H = ( LHyp ` K )
  assume dihord5apre.j: |- .\/ = ( join ` K )
  assume dihord5apre.m: |- ./\ = ( meet ` K )
  assume dihord5apre.a: |- A = ( Atoms ` K )
  assume dihord5apre.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihord5apre.s: |- .(+) = ( LSSum ` U )
  assume dihord5apre.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ -. Y .<_ W ) ) /\ ( I ` X ) C_ ( I ` Y ) ) -> X .<_ Y )

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
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    wss
    #
    wa
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @14
    cY
    cW
    c.an
    co
    #
    c.or
    co
    cY
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    cX
    cY
    c.le
    wbr
    #
    @13
    @2
    @8
    @20
    @2
    @5
    @8
    @12
    simpl1
    @2
    @5
    @8
    @12
    simpl3
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cY
    vr
    dihord5apre.b
    dihord5apre.l
    dihord5apre.j
    dihord5apre.m
    dihord5apre.a
    dihord5apre.h
    lhpmcvr2
    syl2anc
    @13
    @19
    @21
    vr
    cA
    @13
    @14
    cA
    wcel
    #
    @16
    @18
    @21
    @13
    @22
    @16
    @18
    @21
    @9
    @12
    @22
    @16
    wa
    #
    @18
    wa
    #
    @21
    @9
    @12
    @24
    w3a
    #
    cB
    cK
    c.le
    cX
    @14
    cX
    c.or
    co
    #
    cY
    dihord5apre.b
    dihord5apre.l
    @25
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @12
    @24
    simp11l
    cK
    hllat
    syl
    #
    @3
    @4
    @2
    @8
    @12
    @24
    simp12l
    #
    @25
    @27
    @14
    cB
    wcel
    #
    @3
    @26
    cB
    wcel
    #
    @28
    @25
    @22
    @30
    @22
    @16
    @18
    @9
    @12
    simp3ll
    cA
    cB
    @14
    cK
    dihord5apre.b
    dihord5apre.a
    atbase
    syl
    #
    @29
    cB
    c.or
    cK
    @14
    cX
    dihord5apre.b
    dihord5apre.j
    latjcl
    syl3anc
    #
    @6
    @7
    @2
    @5
    @12
    @24
    simp13l
    #
    @25
    @27
    @30
    @3
    cX
    @26
    c.le
    wbr
    @28
    @32
    @29
    cB
    c.or
    cK
    c.le
    @14
    cX
    dihord5apre.b
    dihord5apre.l
    dihord5apre.j
    latlej2
    syl3anc
    @25
    @26
    cI
    cfv
    #
    @11
    wss
    #
    @26
    cY
    c.le
    wbr
    #
    @25
    @35
    @14
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    @26
    cW
    c.an
    co
    #
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    c.po
    co
    #
    @11
    @25
    @2
    @31
    @26
    cW
    c.le
    wbr
    #
    wn
    #
    @23
    @14
    @40
    c.or
    co
    @26
    wceq
    @35
    @43
    wceq
    @2
    @5
    @8
    @12
    @24
    simp11
    #
    @33
    @25
    @44
    @15
    @22
    @16
    @18
    @9
    @12
    simp3lr
    @25
    @14
    @26
    c.le
    wbr
    #
    @44
    @15
    @25
    @27
    @30
    @3
    @47
    @28
    @32
    @29
    cB
    c.or
    cK
    c.le
    @14
    cX
    dihord5apre.b
    dihord5apre.l
    dihord5apre.j
    latlej1
    syl3anc
    @25
    @27
    @30
    @31
    cW
    cB
    wcel
    #
    @47
    @44
    wa
    @15
    wi
    @28
    @32
    @33
    @25
    @1
    @48
    @0
    @1
    @5
    @8
    @12
    @24
    simp11r
    cB
    cH
    cK
    cW
    dihord5apre.b
    dihord5apre.h
    lhpbase
    syl
    #
    cB
    cK
    c.le
    @14
    @26
    cW
    dihord5apre.b
    dihord5apre.l
    lattr
    syl13anc
    mpand
    mtod
    #
    @9
    @12
    @23
    @18
    simp3l
    #
    @25
    @40
    cX
    @14
    c.or
    @25
    @2
    @23
    @5
    @40
    cX
    wceq
    @46
    @51
    @2
    @5
    @8
    @12
    @24
    simp12
    #
    cA
    cB
    @14
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihord5apre.b
    dihord5apre.l
    dihord5apre.j
    dihord5apre.m
    dihord5apre.a
    dihord5apre.h
    lhple
    syl3anc
    #
    oveq2d
    cA
    cB
    @38
    @41
    c.po
    @14
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    @26
    dihord5apre.b
    dihord5apre.l
    dihord5apre.j
    dihord5apre.m
    dihord5apre.a
    dihord5apre.h
    dihord5apre.i
    @41
    eqid
    #
    @38
    eqid
    #
    dihord5apre.u
    dihord5apre.s
    dihvalcq
    syl122anc
    @25
    @39
    @11
    wss
    #
    @42
    @11
    wss
    #
    @43
    @11
    wss
    #
    @25
    @39
    @39
    @17
    @41
    cfv
    #
    c.po
    co
    #
    @11
    @25
    @39
    cU
    csubg
    cfv
    #
    wcel
    #
    @59
    @61
    wcel
    @39
    @60
    wss
    @25
    cU
    clss
    cfv
    #
    @61
    @39
    @25
    cU
    clmod
    wcel
    @63
    @61
    wss
    @25
    cU
    cH
    cK
    cW
    dihord5apre.h
    dihord5apre.u
    @46
    dvhlmod
    @63
    cU
    @63
    eqid
    #
    lsssssubg
    syl
    #
    @25
    @2
    @23
    @39
    @63
    wcel
    @46
    @51
    cA
    @14
    @63
    cU
    cH
    @38
    cK
    c.le
    cW
    dihord5apre.l
    dihord5apre.a
    dihord5apre.h
    dihord5apre.u
    @55
    @64
    diclss
    syl2anc
    sseldd
    #
    @25
    @63
    @61
    @59
    @65
    @25
    @2
    @17
    cB
    wcel
    #
    @17
    cW
    c.le
    wbr
    #
    @59
    @63
    wcel
    @46
    @25
    @27
    @6
    @48
    @67
    @28
    @34
    @49
    cB
    cK
    c.an
    cY
    cW
    dihord5apre.b
    dihord5apre.m
    latmcl
    syl3anc
    @25
    @27
    @6
    @48
    @68
    @28
    @34
    @49
    cB
    cK
    c.le
    c.an
    cY
    cW
    dihord5apre.b
    dihord5apre.l
    dihord5apre.m
    latmle2
    syl3anc
    cB
    @63
    cU
    cH
    @41
    cK
    c.le
    cW
    @17
    dihord5apre.b
    dihord5apre.l
    dihord5apre.h
    dihord5apre.u
    @54
    @64
    diblss
    syl12anc
    sseldd
    c.po
    @39
    @59
    cU
    dihord5apre.s
    lsmub1
    syl2anc
    @25
    @2
    @8
    @23
    @18
    @11
    @60
    wceq
    @46
    @2
    @5
    @8
    @12
    @24
    simp13
    #
    @51
    @9
    @12
    @23
    @18
    simp3r
    cA
    cB
    @38
    @41
    c.po
    @14
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cY
    dihord5apre.b
    dihord5apre.l
    dihord5apre.j
    dihord5apre.m
    dihord5apre.a
    dihord5apre.h
    dihord5apre.i
    @54
    @55
    dihord5apre.u
    dihord5apre.s
    dihvalcq
    syl112anc
    sseqtr4d
    @25
    @42
    @10
    @11
    @25
    @42
    cX
    @41
    cfv
    #
    @10
    @25
    @40
    cX
    @41
    @53
    fveq2d
    @25
    @2
    @5
    @10
    @70
    wceq
    @46
    @52
    cB
    @41
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dihord5apre.b
    dihord5apre.l
    dihord5apre.h
    dihord5apre.i
    @54
    dihvalb
    syl2anc
    eqtr4d
    @9
    @12
    @24
    simp2
    eqsstrd
    @25
    @62
    @42
    @61
    wcel
    @11
    @61
    wcel
    @56
    @57
    wa
    @58
    wb
    @66
    @25
    @63
    @61
    @42
    @65
    @25
    @2
    @40
    cB
    wcel
    #
    @40
    cW
    c.le
    wbr
    #
    @42
    @63
    wcel
    @46
    @25
    @27
    @31
    @48
    @71
    @28
    @33
    @49
    cB
    cK
    c.an
    @26
    cW
    dihord5apre.b
    dihord5apre.m
    latmcl
    syl3anc
    @25
    @27
    @31
    @48
    @72
    @28
    @33
    @49
    cB
    cK
    c.le
    c.an
    @26
    cW
    dihord5apre.b
    dihord5apre.l
    dihord5apre.m
    latmle2
    syl3anc
    cB
    @63
    cU
    cH
    @41
    cK
    c.le
    cW
    @40
    dihord5apre.b
    dihord5apre.l
    dihord5apre.h
    dihord5apre.u
    @54
    @64
    diblss
    syl12anc
    sseldd
    @25
    @63
    @61
    @11
    @65
    @25
    @2
    @6
    @11
    @63
    wcel
    @46
    @34
    cB
    @63
    cU
    cH
    cI
    cK
    cW
    cY
    dihord5apre.b
    dihord5apre.h
    dihord5apre.i
    dihord5apre.u
    @64
    dihlss
    syl2anc
    sseldd
    c.po
    @39
    @42
    @11
    cU
    dihord5apre.s
    lsmlub
    syl3anc
    mpbi2and
    eqsstrd
    @25
    @2
    @31
    @45
    @8
    @36
    @37
    wb
    @46
    @33
    @50
    @69
    cB
    cH
    cI
    cK
    c.le
    cW
    @26
    cY
    dihord5apre.b
    dihord5apre.l
    dihord5apre.h
    dihord5apre.i
    dihord4
    syl121anc
    mpbid
    lattrd
    3expia
    exp4c
    imp4a
    rexlimdv
    mpd
end
