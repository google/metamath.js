include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cplt.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "simpr.mm"
include "wn.mm"
include "simpl1.mm"
include "simpl3.mm"
include "lplnnelln.mm"
include "syl2anc.mm"
include "wceq.mm"
include "simpl2.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "wb.mm"
include "eqid.mm"
include "pltval.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "cv.mm"
include "cjn.mm"
include "co.mm"
include "catm.mm"
include "wrex.mm"
include "cbs.mm"
include "llnbase.mm"
include "syl.mm"
include "lplnbase.mm"
include "hlrelat3.mm"
include "syl31anc.mm"
include "wi.mm"
include "islpln2.mm"
include "simp3.mm"
include "islln2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "simp12r.mm"
include "oveq1d.mm"
include "simp22.mm"
include "3brtr3d.mm"
include "simp111.mm"
include "simp112.mm"
include "simp113.mm"
include "simp23.mm"
include "3jca.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp21.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "cvr1.mm"
include "mpbird.mm"
include "simp12l.mm"
include "3at.mm"
include "syl32anc.mm"
include "mpbid.mm"
include "3eqtr4d.mm"
include "breqtrd.mm"
include "3exp.mm"
include "3expd.mm"
include "3expib.mm"
include "rexlimdvv.mm"
include "adantld.mm"
include "sylbid.mm"
include "imp31.mm"
include "syl7.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"
include "3impia.mm"
include "imp.mm"
include "syldan.mm"

theorem llncvrlpln2
  let cC: class C
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume llncvrlpln2.l: |- .<_ = ( le ` K )
  assume llncvrlpln2.c: |- C = ( <o ` K )
  assume llncvrlpln2.n: |- N = ( LLines ` K )
  assume llncvrlpln2.p: |- P = ( LPlanes ` K )


  assert |- ( ( ( K e. HL /\ X e. N /\ Y e. P ) /\ X .<_ Y ) -> X C Y )

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
    cP
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    cK
    cplt
    cfv
    #
    wbr
    #
    cX
    cY
    cC
    wbr
    #
    @3
    @4
    wa
    #
    @6
    @4
    cX
    cY
    wne
    #
    @3
    @4
    simpr
    @8
    cY
    cN
    wcel
    #
    wn
    #
    @9
    @8
    @0
    @2
    @11
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl3
    cP
    cK
    cN
    cY
    llncvrlpln2.n
    llncvrlpln2.p
    lplnnelln
    syl2anc
    @8
    @10
    cX
    cY
    @8
    @1
    cX
    cY
    wceq
    @10
    @0
    @1
    @2
    @4
    simpl2
    cX
    cY
    cN
    eleq1
    syl5ibcom
    necon3bd
    mpd
    @3
    @6
    @4
    @9
    wa
    wb
    @4
    chlt
    cN
    cP
    @5
    cK
    c.le
    cX
    cY
    llncvrlpln2.l
    @5
    eqid
    #
    pltval
    adantr
    mpbir2and
    @3
    @6
    cX
    cX
    vr
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cC
    wbr
    #
    @15
    cY
    c.le
    wbr
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
    @7
    @3
    @6
    wa
    #
    @0
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    cY
    @22
    wcel
    #
    @6
    @20
    @0
    @1
    @2
    @6
    simpl1
    @21
    @1
    @23
    @0
    @1
    @2
    @6
    simpl2
    @22
    cK
    cN
    cX
    @22
    eqid
    #
    llncvrlpln2.n
    llnbase
    syl
    @21
    @2
    @24
    @0
    @1
    @2
    @6
    simpl3
    @22
    cP
    cK
    cY
    @25
    llncvrlpln2.p
    lplnbase
    syl
    @3
    @6
    simpr
    @19
    @22
    cC
    @5
    @14
    cK
    c.le
    cX
    cY
    vr
    @25
    llncvrlpln2.l
    @12
    @14
    eqid
    #
    llncvrlpln2.c
    @19
    eqid
    #
    hlrelat3
    syl31anc
    @3
    @20
    @7
    @3
    @18
    @7
    vr
    @19
    @0
    @1
    @2
    @13
    @19
    wcel
    #
    @18
    @7
    wi
    #
    wi
    #
    @0
    @1
    wa
    #
    @2
    @24
    vs
    cv
    #
    vt
    cv
    #
    wne
    #
    vu
    cv
    #
    @32
    @33
    @14
    co
    #
    c.le
    wbr
    wn
    #
    cY
    @36
    @35
    @14
    co
    #
    wceq
    #
    w3a
    #
    vu
    @19
    wrex
    #
    vt
    @19
    wrex
    vs
    @19
    wrex
    #
    wa
    #
    @30
    @0
    @2
    @43
    wb
    @1
    @19
    @22
    cP
    @14
    cK
    c.le
    cY
    vu
    vt
    vs
    @25
    llncvrlpln2.l
    @26
    @27
    llncvrlpln2.p
    islpln2
    adantr
    @31
    @42
    @30
    @24
    @31
    @41
    @30
    vs
    vt
    @19
    @19
    @31
    @32
    @19
    wcel
    #
    @33
    @19
    wcel
    #
    wa
    #
    wa
    #
    @40
    @30
    vu
    @19
    @40
    @39
    @47
    @35
    @19
    wcel
    #
    @30
    @34
    @37
    @39
    simp3
    @0
    @1
    @46
    @48
    @39
    @30
    wi
    wi
    #
    @0
    @1
    @23
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cX
    @50
    @51
    @14
    co
    #
    wceq
    #
    wa
    #
    vq
    @19
    wrex
    vp
    @19
    wrex
    #
    wa
    @46
    @49
    wi
    #
    @19
    @22
    @14
    cK
    cN
    cX
    vq
    vp
    @25
    @26
    @27
    llncvrlpln2.n
    islln2
    @0
    @56
    @57
    @23
    @0
    @55
    @57
    vp
    vq
    @19
    @19
    @0
    @50
    @19
    wcel
    #
    @51
    @19
    wcel
    #
    @55
    @57
    wi
    @0
    @58
    @59
    w3a
    #
    @55
    @46
    @49
    @60
    @55
    @46
    w3a
    #
    @48
    @39
    @28
    @29
    @61
    @48
    @39
    @28
    w3a
    #
    @18
    @7
    @61
    @62
    @18
    w3a
    #
    cX
    @15
    cY
    cC
    @61
    @62
    @16
    @17
    simp3l
    #
    @63
    @53
    @13
    @14
    co
    #
    @38
    @15
    cY
    @63
    @65
    @38
    c.le
    wbr
    #
    @65
    @38
    wceq
    #
    @63
    @15
    cY
    @65
    @38
    c.le
    @61
    @62
    @16
    @17
    simp3r
    @63
    cX
    @53
    @13
    @14
    @52
    @54
    @60
    @46
    @62
    @18
    simp12r
    #
    oveq1d
    #
    @61
    @48
    @39
    @28
    @18
    simp22
    #
    3brtr3d
    @63
    @0
    @58
    @59
    @28
    w3a
    @44
    @45
    @48
    w3a
    @13
    @53
    c.le
    wbr
    wn
    #
    @52
    @66
    @67
    wb
    @0
    @58
    @59
    @55
    @46
    @62
    @18
    simp111
    #
    @63
    @58
    @59
    @28
    @0
    @58
    @59
    @55
    @46
    @62
    @18
    simp112
    #
    @0
    @58
    @59
    @55
    @46
    @62
    @18
    simp113
    #
    @61
    @48
    @39
    @28
    @18
    simp23
    #
    3jca
    @63
    @44
    @45
    @48
    @44
    @45
    @60
    @55
    @62
    @18
    simp13l
    @44
    @45
    @60
    @55
    @62
    @18
    simp13r
    @61
    @48
    @39
    @28
    @18
    simp21
    3jca
    @63
    @71
    @53
    @65
    cC
    wbr
    #
    @63
    cX
    @15
    @53
    @65
    cC
    @64
    @68
    @69
    3brtr3d
    @63
    @0
    @53
    @22
    wcel
    #
    @28
    @71
    @76
    wb
    @72
    @63
    @0
    @58
    @59
    @77
    @72
    @73
    @74
    @19
    @22
    @14
    cK
    @50
    @51
    @25
    @26
    @27
    hlatjcl
    syl3anc
    @75
    @19
    @22
    cC
    @13
    @14
    cK
    c.le
    @53
    @25
    llncvrlpln2.l
    @26
    llncvrlpln2.c
    @27
    cvr1
    syl3anc
    mpbird
    @52
    @54
    @60
    @46
    @62
    @18
    simp12l
    @19
    @50
    @51
    @13
    @32
    @33
    @35
    @14
    cK
    c.le
    llncvrlpln2.l
    @26
    @27
    3at
    syl32anc
    mpbid
    @69
    @70
    3eqtr4d
    breqtrd
    3exp
    3expd
    3exp
    3expib
    rexlimdvv
    adantld
    sylbid
    imp31
    syl7
    rexlimdv
    rexlimdvva
    adantld
    sylbid
    3impia
    rexlimdv
    imp
    syldan
    syldan
end
