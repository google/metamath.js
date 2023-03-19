include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl2.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simpl1.mm"
include "eqid.mm"
include "lplnbase.mm"
include "syl.mm"
include "islpln3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wi.mm"
include "wne.mm"
include "simpll1.mm"
include "simpr2l.mm"
include "simpll3.mm"
include "simpr1.mm"
include "llnexatN.mm"
include "syl31anc.mm"
include "simp1l1.mm"
include "simp22r.mm"
include "simp3l.mm"
include "simp1l3.mm"
include "simp23l.mm"
include "simp3rr.mm"
include "breq2d.mm"
include "mtbid.mm"
include "atnlej2.mm"
include "syl131anc.mm"
include "llni2.mm"
include "simp3rl.mm"
include "hlatcon2.mm"
include "syl132anc.mm"
include "simp23r.mm"
include "oveq1d.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "latj31.mm"
include "syl13anc.mm"
include "3eqtrd.mm"
include "breq2.mm"
include "notbid.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "3exp2.mm"
include "llnbase.mm"
include "simpr2r.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simpr3r.mm"
include "breqtrrd.mm"
include "simplr.mm"
include "simpll2.mm"
include "latjle12.mm"
include "mpbi2and.mm"
include "ccvr.mm"
include "latjcl.mm"
include "cvr1.mm"
include "lplni.mm"
include "lplncmp.mm"
include "eqcomd.mm"
include "weq.mm"
include "pm2.61d.mm"
include "rexlimdvv.mm"

theorem lplnexllnN
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vq: setvar q
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  assume lplnexat.l: |- .<_ = ( le ` K )
  assume lplnexat.j: |- .\/ = ( join ` K )
  assume lplnexat.a: |- A = ( Atoms ` K )
  assume lplnexat.n: |- N = ( LLines ` K )
  assume lplnexat.p: |- P = ( LPlanes ` K )

  disjoint .\/ y
  disjoint .<_ y
  disjoint N y
  disjoint Q y
  disjoint X y
  disjoint A q
  disjoint K q
  disjoint .<_ q
  disjoint Y q
  disjoint X q
  disjoint r s
  disjoint r z
  disjoint A r
  disjoint s z
  disjoint A s
  disjoint A z
  disjoint r y
  disjoint .\/ r
  disjoint s y
  disjoint .\/ s
  disjoint y z
  disjoint .\/ z
  disjoint K r
  disjoint K s
  disjoint K z
  disjoint .<_ r
  disjoint .<_ s
  disjoint .<_ z
  disjoint N r
  disjoint N s
  disjoint N z
  disjoint P r
  disjoint P s
  disjoint P z
  disjoint Q r
  disjoint Q s
  disjoint Q z
  disjoint X r
  disjoint X s
  disjoint X z
  assert |- ( ( ( K e. HL /\ X e. P /\ Q e. A ) /\ Q .<_ X ) -> E. y e. N ( -. Q .<_ y /\ X = ( y .\/ Q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cQ
    cX
    c.le
    wbr
    #
    wa
    #
    vr
    cv
    #
    vz
    cv
    #
    c.le
    wbr
    #
    wn
    #
    cX
    @7
    @6
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
    vz
    cN
    wrex
    #
    cQ
    vy
    cv
    #
    c.le
    wbr
    #
    wn
    #
    cX
    @14
    cQ
    c.or
    co
    #
    wceq
    #
    wa
    #
    vy
    cN
    wrex
    #
    @5
    @1
    @13
    @0
    @1
    @2
    @4
    simpl2
    #
    @5
    @0
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @1
    @13
    wb
    @0
    @1
    @2
    @4
    simpl1
    @5
    @1
    @23
    @21
    @22
    cP
    cK
    cX
    @22
    eqid
    #
    lplnexat.p
    lplnbase
    #
    syl
    vz
    cA
    @22
    cP
    c.or
    cK
    c.le
    cN
    cX
    vr
    @24
    lplnexat.l
    lplnexat.j
    lplnexat.a
    lplnexat.n
    lplnexat.p
    islpln3
    syl2anc
    mpbid
    @5
    @12
    @20
    vz
    vr
    cN
    cA
    @5
    cQ
    @7
    c.le
    wbr
    #
    @7
    cN
    wcel
    #
    @6
    cA
    wcel
    #
    wa
    #
    @12
    @20
    wi
    wi
    @5
    @26
    @29
    @12
    @20
    @5
    @26
    @29
    @12
    w3a
    #
    wa
    #
    cQ
    vs
    cv
    #
    wne
    #
    @7
    cQ
    @32
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
    @20
    @31
    @0
    @27
    @2
    @26
    @37
    @0
    @1
    @2
    @4
    @30
    simpll1
    @27
    @28
    @26
    @12
    @5
    simpr2l
    @0
    @1
    @2
    @4
    @30
    simpll3
    @5
    @26
    @29
    @12
    simpr1
    cA
    cQ
    c.or
    cK
    c.le
    cN
    @7
    vs
    lplnexat.l
    lplnexat.j
    lplnexat.a
    lplnexat.n
    llnexatN
    syl31anc
    @31
    @36
    @20
    vs
    cA
    @31
    @32
    cA
    wcel
    #
    @36
    @20
    @5
    @30
    @38
    @36
    wa
    #
    @20
    @5
    @30
    @39
    w3a
    #
    @6
    @32
    c.or
    co
    #
    cN
    wcel
    #
    cQ
    @41
    c.le
    wbr
    #
    wn
    #
    cX
    @41
    cQ
    c.or
    co
    #
    wceq
    #
    @20
    @40
    @0
    @28
    @38
    @6
    @32
    wne
    #
    @42
    @0
    @1
    @2
    @4
    @30
    @39
    simp1l1
    #
    @27
    @28
    @26
    @12
    @5
    @39
    simp22r
    #
    @5
    @30
    @38
    @36
    simp3l
    #
    @40
    @0
    @28
    @2
    @38
    @6
    @34
    c.le
    wbr
    #
    wn
    #
    @47
    @48
    @49
    @0
    @1
    @2
    @4
    @30
    @39
    simp1l3
    #
    @50
    @40
    @8
    @51
    @9
    @11
    @26
    @29
    @5
    @39
    simp23l
    @40
    @7
    @34
    @6
    c.le
    @33
    @35
    @38
    @5
    @30
    simp3rr
    #
    breq2d
    mtbid
    #
    cA
    @6
    cQ
    @32
    c.or
    cK
    c.le
    lplnexat.l
    lplnexat.j
    lplnexat.a
    atnlej2
    syl131anc
    cA
    @6
    @32
    c.or
    cK
    cN
    lplnexat.j
    lplnexat.a
    lplnexat.n
    llni2
    syl31anc
    @40
    @0
    @2
    @38
    @28
    @33
    @52
    @44
    @48
    @53
    @50
    @49
    @33
    @35
    @38
    @5
    @30
    simp3rl
    @55
    cA
    cQ
    @32
    @6
    c.or
    cK
    c.le
    lplnexat.l
    lplnexat.j
    lplnexat.a
    hlatcon2
    syl132anc
    @40
    cX
    @10
    @34
    @6
    c.or
    co
    #
    @45
    @9
    @11
    @26
    @29
    @5
    @39
    simp23r
    @40
    @7
    @34
    @6
    c.or
    @54
    oveq1d
    @40
    cK
    clat
    wcel
    #
    cQ
    @22
    wcel
    #
    @32
    @22
    wcel
    #
    @6
    @22
    wcel
    #
    @56
    @45
    wceq
    @40
    @0
    @57
    @48
    cK
    hllat
    #
    syl
    @40
    @2
    @58
    @53
    cA
    @22
    cQ
    cK
    @24
    lplnexat.a
    atbase
    #
    syl
    @40
    @38
    @59
    @50
    cA
    @22
    @32
    cK
    @24
    lplnexat.a
    atbase
    syl
    @40
    @28
    @60
    @49
    cA
    @22
    @6
    cK
    @24
    lplnexat.a
    atbase
    #
    syl
    @22
    c.or
    cK
    cQ
    @32
    @6
    @24
    lplnexat.j
    latj31
    syl13anc
    3eqtrd
    @19
    @44
    @46
    wa
    vy
    @41
    cN
    @14
    @41
    wceq
    #
    @16
    @44
    @18
    @46
    @64
    @15
    @43
    @14
    @41
    cQ
    c.le
    breq2
    notbid
    @64
    @17
    @45
    cX
    @14
    @41
    cQ
    c.or
    oveq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    3expia
    expd
    rexlimdv
    mpd
    3exp2
    @5
    @26
    wn
    #
    @29
    @12
    @20
    @5
    @65
    @29
    @12
    w3a
    #
    wa
    #
    @27
    @65
    cX
    @7
    cQ
    c.or
    co
    #
    wceq
    #
    @20
    @27
    @28
    @65
    @12
    @5
    simpr2l
    #
    @5
    @65
    @29
    @12
    simpr1
    #
    @67
    @68
    cX
    @67
    @68
    cX
    c.le
    wbr
    #
    @68
    cX
    wceq
    #
    @67
    @7
    cX
    c.le
    wbr
    #
    @4
    @72
    @67
    @7
    @10
    cX
    c.le
    @67
    @57
    @7
    @22
    wcel
    #
    @60
    @7
    @10
    c.le
    wbr
    @67
    @0
    @57
    @0
    @1
    @2
    @4
    @66
    simpll1
    #
    @61
    syl
    #
    @67
    @27
    @75
    @70
    @22
    cK
    cN
    @7
    @24
    lplnexat.n
    llnbase
    syl
    #
    @67
    @28
    @60
    @27
    @28
    @65
    @12
    @5
    simpr2r
    @63
    syl
    @22
    c.or
    cK
    c.le
    @7
    @6
    @24
    lplnexat.l
    lplnexat.j
    latlej1
    syl3anc
    @9
    @11
    @65
    @29
    @5
    simpr3r
    breqtrrd
    @3
    @4
    @66
    simplr
    @67
    @57
    @75
    @58
    @23
    @74
    @4
    wa
    @72
    wb
    @77
    @78
    @67
    @2
    @58
    @0
    @1
    @2
    @4
    @66
    simpll3
    #
    @62
    syl
    #
    @67
    @1
    @23
    @0
    @1
    @2
    @4
    @66
    simpll2
    #
    @25
    syl
    @22
    c.or
    cK
    c.le
    @7
    cQ
    cX
    @24
    lplnexat.l
    lplnexat.j
    latjle12
    syl13anc
    mpbi2and
    @67
    @0
    @68
    cP
    wcel
    #
    @1
    @72
    @73
    wb
    @76
    @67
    @0
    @68
    @22
    wcel
    #
    @27
    @7
    @68
    cK
    ccvr
    cfv
    #
    wbr
    #
    @82
    @76
    @67
    @57
    @75
    @58
    @83
    @77
    @78
    @80
    @22
    c.or
    cK
    @7
    cQ
    @24
    lplnexat.j
    latjcl
    syl3anc
    @70
    @67
    @65
    @85
    @71
    @67
    @0
    @75
    @2
    @65
    @85
    wb
    @76
    @78
    @79
    cA
    @22
    @84
    cQ
    c.or
    cK
    c.le
    @7
    @24
    lplnexat.l
    lplnexat.j
    @84
    eqid
    #
    lplnexat.a
    cvr1
    syl3anc
    mpbid
    @22
    @84
    chlt
    cP
    cK
    cN
    @7
    @68
    @24
    @86
    lplnexat.n
    lplnexat.p
    lplni
    syl31anc
    @81
    cP
    cK
    c.le
    @68
    cX
    lplnexat.l
    lplnexat.p
    lplncmp
    syl3anc
    mpbid
    eqcomd
    @19
    @65
    @69
    wa
    vy
    @7
    cN
    vy
    vz
    weq
    #
    @16
    @65
    @18
    @69
    @87
    @15
    @26
    @14
    @7
    cQ
    c.le
    breq2
    notbid
    @87
    @17
    @68
    cX
    @14
    @7
    cQ
    c.or
    oveq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    3exp2
    pm2.61d
    rexlimdvv
    mpd
end
