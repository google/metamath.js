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
include "lvolnelpln.mm"
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
include "lplnbase.mm"
include "syl.mm"
include "lvolbase.mm"
include "hlrelat3.mm"
include "syl31anc.mm"
include "wi.mm"
include "islvol2.mm"
include "islpln2.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "simp133.mm"
include "oveq1d.mm"
include "simp23.mm"
include "3brtr3d.mm"
include "simp11.mm"
include "simp12.mm"
include "simp3l.mm"
include "simp21l.mm"
include "3jca.mm"
include "simp21r.mm"
include "simp22l.mm"
include "simp22r.mm"
include "simp131.mm"
include "simp132.mm"
include "simp111.mm"
include "clat.mm"
include "hllat.mm"
include "hlatjcl.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "cvr1.mm"
include "mpbird.mm"
include "4at2.mm"
include "syl33anc.mm"
include "mpbid.mm"
include "3eqtr4d.mm"
include "breqtrd.mm"
include "3exp.mm"
include "exp4a.mm"
include "3expd.mm"
include "rexlimdv3a.mm"
include "3expib.mm"
include "rexlimdvv.mm"
include "adantld.mm"
include "sylbid.mm"
include "imp31.mm"
include "syl7.mm"
include "rexlimdvva.mm"
include "3impia.mm"
include "rexlimdv.mm"
include "imp.mm"
include "syldan.mm"

theorem lplncvrlvol2
  let cC: class C
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume lplncvrlvol2.l: |- .<_ = ( le ` K )
  assume lplncvrlvol2.c: |- C = ( <o ` K )
  assume lplncvrlvol2.p: |- P = ( LPlanes ` K )
  assume lplncvrlvol2.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. HL /\ X e. P /\ Y e. V ) /\ X .<_ Y ) -> X C Y )

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
    cV
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
    cP
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
    cV
    cY
    lplncvrlvol2.p
    lplncvrlvol2.v
    lvolnelpln
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
    cP
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
    cP
    cV
    @5
    cK
    c.le
    cX
    cY
    lplncvrlvol2.l
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
    vs
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
    vs
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
    cP
    cK
    cX
    @22
    eqid
    #
    lplncvrlvol2.p
    lplnbase
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
    cK
    cV
    cY
    @25
    lplncvrlvol2.v
    lvolbase
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
    vs
    @25
    lplncvrlvol2.l
    @12
    @14
    eqid
    #
    lplncvrlvol2.c
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
    vs
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
    wi
    #
    @0
    @1
    wa
    #
    @2
    @24
    vt
    cv
    #
    vu
    cv
    #
    wne
    vv
    cv
    #
    @31
    @32
    @14
    co
    #
    c.le
    wbr
    wn
    vw
    cv
    #
    @34
    @33
    @14
    co
    #
    c.le
    wbr
    wn
    w3a
    #
    cY
    @36
    @35
    @14
    co
    #
    wceq
    #
    wa
    #
    vw
    @19
    wrex
    vv
    @19
    wrex
    #
    vu
    @19
    wrex
    vt
    @19
    wrex
    #
    wa
    #
    @29
    @0
    @2
    @43
    wb
    @1
    @19
    @22
    @14
    cK
    c.le
    cV
    cY
    vw
    vv
    vu
    vt
    @25
    lplncvrlvol2.l
    @26
    @27
    lplncvrlvol2.v
    islvol2
    adantr
    @30
    @42
    @29
    @24
    @30
    @41
    @29
    vt
    vu
    @19
    @19
    @30
    @31
    @19
    wcel
    #
    @32
    @19
    wcel
    #
    wa
    #
    wa
    #
    @40
    @29
    vv
    vw
    @19
    @19
    @40
    @39
    @47
    @33
    @19
    wcel
    #
    @35
    @19
    wcel
    #
    wa
    #
    @29
    @37
    @39
    simpr
    @0
    @1
    @46
    @50
    @39
    @29
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
    vr
    cv
    #
    @52
    @53
    @14
    co
    #
    c.le
    wbr
    wn
    #
    cX
    @56
    @55
    @14
    co
    #
    wceq
    #
    w3a
    #
    vr
    @19
    wrex
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
    @51
    wi
    #
    @19
    @22
    cP
    @14
    cK
    c.le
    cX
    vr
    vq
    vp
    @25
    lplncvrlvol2.l
    @26
    @27
    lplncvrlvol2.p
    islpln2
    @0
    @62
    @63
    @23
    @0
    @61
    @63
    vp
    vq
    @19
    @19
    @0
    @52
    @19
    wcel
    #
    @53
    @19
    wcel
    #
    @61
    @63
    wi
    @0
    @64
    @65
    w3a
    #
    @60
    @63
    vr
    @19
    @66
    @55
    @19
    wcel
    #
    @60
    w3a
    #
    @46
    @50
    @39
    @29
    @68
    @46
    @50
    @39
    w3a
    #
    @28
    @18
    @7
    @68
    @69
    @28
    @18
    wa
    #
    @7
    @68
    @69
    @70
    w3a
    #
    cX
    @15
    cY
    cC
    @16
    @17
    @28
    @68
    @69
    simp3rl
    #
    @71
    @58
    @13
    @14
    co
    #
    @38
    @15
    cY
    @71
    @73
    @38
    c.le
    wbr
    #
    @73
    @38
    wceq
    #
    @71
    @15
    cY
    @73
    @38
    c.le
    @16
    @17
    @28
    @68
    @69
    simp3rr
    @71
    cX
    @58
    @13
    @14
    @54
    @57
    @59
    @66
    @67
    @69
    @70
    simp133
    #
    oveq1d
    #
    @68
    @46
    @50
    @39
    @70
    simp23
    #
    3brtr3d
    @71
    @66
    @67
    @28
    @44
    w3a
    @45
    @48
    @49
    w3a
    @54
    @57
    @13
    @58
    c.le
    wbr
    wn
    #
    @74
    @75
    wb
    @66
    @67
    @60
    @69
    @70
    simp11
    #
    @71
    @67
    @28
    @44
    @66
    @67
    @60
    @69
    @70
    simp12
    #
    @68
    @69
    @28
    @18
    simp3l
    #
    @44
    @45
    @50
    @39
    @68
    @70
    simp21l
    3jca
    @71
    @45
    @48
    @49
    @44
    @45
    @50
    @39
    @68
    @70
    simp21r
    @48
    @49
    @46
    @39
    @68
    @70
    simp22l
    @48
    @49
    @46
    @39
    @68
    @70
    simp22r
    3jca
    @54
    @57
    @59
    @66
    @67
    @69
    @70
    simp131
    @54
    @57
    @59
    @66
    @67
    @69
    @70
    simp132
    @71
    @79
    @58
    @73
    cC
    wbr
    #
    @71
    cX
    @15
    @58
    @73
    cC
    @72
    @76
    @77
    3brtr3d
    @71
    @0
    @58
    @22
    wcel
    #
    @28
    @79
    @83
    wb
    @0
    @64
    @65
    @67
    @60
    @69
    @70
    simp111
    #
    @71
    cK
    clat
    wcel
    #
    @56
    @22
    wcel
    #
    @55
    @22
    wcel
    #
    @84
    @71
    @0
    @86
    @85
    cK
    hllat
    syl
    @71
    @66
    @87
    @80
    @19
    @22
    @14
    cK
    @52
    @53
    @25
    @26
    @27
    hlatjcl
    syl
    @71
    @67
    @88
    @81
    @19
    @22
    @55
    cK
    @25
    @27
    atbase
    syl
    @22
    @14
    cK
    @56
    @55
    @25
    @26
    latjcl
    syl3anc
    @82
    @19
    @22
    cC
    @13
    @14
    cK
    c.le
    @58
    @25
    lplncvrlvol2.l
    @26
    lplncvrlvol2.c
    @27
    cvr1
    syl3anc
    mpbird
    @19
    @52
    @53
    @55
    @13
    @31
    @32
    @14
    cK
    c.le
    @33
    @35
    lplncvrlvol2.l
    @26
    @27
    4at2
    syl33anc
    mpbid
    @77
    @78
    3eqtr4d
    breqtrd
    3exp
    exp4a
    3expd
    rexlimdv3a
    3expib
    rexlimdvv
    adantld
    sylbid
    imp31
    syl7
    rexlimdvv
    rexlimdvva
    adantld
    sylbid
    3impia
    rexlimdv
    imp
    syldan
    syldan
end
