include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "simp2r.mm"
include "simp3r.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp3l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cv.mm"
include "wn.mm"
include "wrex.mm"
include "3dim2.mm"
include "syl3anc.mm"
include "cp1.mm"
include "ccvr.mm"
include "cops.mm"
include "simp11l.mm"
include "hlop.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcl.mm"
include "latjcl.mm"
include "ncvr1.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wi.mm"
include "club.mm"
include "simpl1l.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "simpr1l.mm"
include "cdm.mm"
include "cglb.mm"
include "op01dm.mm"
include "simpld.mm"
include "ple1.mm"
include "cpo.mm"
include "hlpos.mm"
include "op1cl.mm"
include "simpr2l.mm"
include "cvr1.mm"
include "mpbid.mm"
include "simpr3.mm"
include "simpl1r.mm"
include "lhp1cvr.mm"
include "eqbrtrd.mm"
include "cvrcmp.mm"
include "syl132anc.mm"
include "simpr2r.mm"
include "simpr1r.mm"
include "eqbrtrrd.mm"
include "3exp2.mm"
include "3imp.mm"
include "necon3bd.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "pltval.mm"
include "mpbir2and.mm"

theorem lhp2lt
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.lt: class .<
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  assume lhp2lt.l: |- .<_ = ( le ` K )
  assume lhp2lt.s: |- .< = ( lt ` K )
  assume lhp2lt.j: |- .\/ = ( join ` K )
  assume lhp2lt.a: |- A = ( Atoms ` K )
  assume lhp2lt.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ P .<_ W ) /\ ( Q e. A /\ Q .<_ W ) ) -> ( P .\/ Q ) .< W )

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
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cW
    c.lt
    wbr
    #
    @10
    cW
    c.le
    wbr
    #
    @10
    cW
    wne
    #
    @9
    @4
    @7
    @12
    @2
    @3
    @4
    @8
    simp2r
    @2
    @5
    @6
    @7
    simp3r
    @9
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @15
    wcel
    #
    cW
    @15
    wcel
    #
    @4
    @7
    wa
    @12
    wb
    @9
    @0
    @14
    @0
    @1
    @5
    @8
    simp1l
    #
    cK
    hllat
    #
    syl
    @9
    @3
    @16
    @2
    @3
    @4
    @8
    simp2l
    #
    cA
    @15
    cP
    cK
    @15
    eqid
    #
    lhp2lt.a
    atbase
    syl
    @9
    @6
    @17
    @2
    @5
    @6
    @7
    simp3l
    #
    cA
    @15
    cQ
    cK
    @22
    lhp2lt.a
    atbase
    syl
    @9
    @1
    @18
    @0
    @1
    @5
    @8
    simp1r
    #
    @15
    cH
    cK
    cW
    @22
    lhp2lt.h
    lhpbase
    syl
    @15
    c.or
    cK
    c.le
    cP
    cQ
    cW
    @22
    lhp2lt.l
    lhp2lt.j
    latjle12
    syl13anc
    mpbi2and
    @9
    vr
    cv
    #
    @10
    c.le
    wbr
    wn
    #
    vs
    cv
    #
    @10
    @25
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    @13
    @9
    @0
    @3
    @6
    @31
    @19
    @21
    @23
    cA
    cP
    cQ
    c.or
    cK
    c.le
    vs
    vr
    lhp2lt.j
    lhp2lt.l
    lhp2lt.a
    3dim2
    syl3anc
    @9
    @30
    @13
    vr
    vs
    cA
    cA
    @9
    @25
    cA
    wcel
    #
    @27
    cA
    wcel
    #
    wa
    #
    @30
    @13
    @9
    @34
    @30
    w3a
    #
    cK
    cp1
    cfv
    #
    @28
    @27
    c.or
    co
    #
    cK
    ccvr
    cfv
    #
    wbr
    #
    wn
    #
    @13
    @35
    cK
    cops
    wcel
    #
    @37
    @15
    wcel
    #
    @40
    @35
    @0
    @41
    @0
    @1
    @5
    @8
    @34
    @30
    simp11l
    #
    cK
    hlop
    #
    syl
    @35
    @14
    @28
    @15
    wcel
    #
    @27
    @15
    wcel
    #
    @42
    @35
    @0
    @14
    @43
    @20
    syl
    #
    @35
    @14
    @10
    @15
    wcel
    #
    @25
    @15
    wcel
    #
    @45
    @47
    @35
    @0
    @3
    @6
    @48
    @43
    @3
    @4
    @2
    @8
    @34
    @30
    simp12l
    @6
    @7
    @2
    @5
    @34
    @30
    simp13l
    cA
    @15
    c.or
    cK
    cP
    cQ
    @22
    lhp2lt.j
    lhp2lt.a
    hlatjcl
    #
    syl3anc
    @35
    @32
    @49
    @9
    @32
    @33
    @30
    simp2l
    cA
    @15
    @25
    cK
    @22
    lhp2lt.a
    atbase
    #
    syl
    @15
    c.or
    cK
    @10
    @25
    @22
    lhp2lt.j
    latjcl
    #
    syl3anc
    @35
    @33
    @46
    @9
    @32
    @33
    @30
    simp2r
    cA
    @15
    @27
    cK
    @22
    lhp2lt.a
    atbase
    syl
    @15
    c.or
    cK
    @28
    @27
    @22
    lhp2lt.j
    latjcl
    syl3anc
    @15
    @38
    @36
    cK
    @37
    @22
    @36
    eqid
    #
    @38
    eqid
    #
    ncvr1
    syl2anc
    @35
    @39
    @10
    cW
    @9
    @34
    @30
    @10
    cW
    wceq
    #
    @39
    wi
    @9
    @34
    @30
    @55
    @39
    @9
    @34
    @30
    @55
    w3a
    #
    wa
    #
    @28
    @36
    @37
    @38
    @57
    @28
    @36
    c.le
    wbr
    #
    @28
    @36
    wceq
    #
    @57
    @15
    cK
    club
    cfv
    #
    @36
    cK
    c.le
    chlt
    @28
    @22
    @60
    eqid
    #
    lhp2lt.l
    @53
    @0
    @1
    @5
    @8
    @56
    simpl1l
    #
    @57
    @14
    @48
    @49
    @45
    @57
    @0
    @14
    @62
    @20
    syl
    @57
    @0
    @3
    @6
    @48
    @62
    @3
    @4
    @2
    @8
    @56
    simpl2l
    @6
    @7
    @2
    @5
    @56
    simpl3l
    @50
    syl3anc
    #
    @57
    @32
    @49
    @32
    @33
    @30
    @55
    @9
    simpr1l
    #
    @51
    syl
    @52
    syl3anc
    #
    @57
    @41
    @15
    @60
    cdm
    wcel
    #
    @57
    @0
    @41
    @62
    @44
    syl
    #
    @41
    @66
    @15
    cK
    cglb
    cfv
    #
    cdm
    wcel
    @15
    @60
    @68
    cK
    @22
    @61
    @68
    eqid
    op01dm
    simpld
    syl
    ple1
    @57
    cK
    cpo
    wcel
    #
    @45
    @36
    @15
    wcel
    #
    @48
    @10
    @28
    @38
    wbr
    #
    @10
    @36
    @38
    wbr
    @58
    @59
    wb
    @57
    @0
    @69
    @62
    cK
    hlpos
    syl
    @65
    @57
    @41
    @70
    @67
    @15
    @36
    cK
    @22
    @53
    op1cl
    syl
    @63
    @57
    @26
    @71
    @26
    @29
    @34
    @55
    @9
    simpr2l
    @57
    @0
    @48
    @32
    @26
    @71
    wb
    @62
    @63
    @64
    cA
    @15
    @38
    @25
    c.or
    cK
    c.le
    @10
    @22
    lhp2lt.l
    lhp2lt.j
    @54
    lhp2lt.a
    cvr1
    syl3anc
    mpbid
    @57
    @10
    cW
    @36
    @38
    @9
    @34
    @30
    @55
    simpr3
    @57
    @0
    @1
    cW
    @36
    @38
    wbr
    @62
    @0
    @1
    @5
    @8
    @56
    simpl1r
    chlt
    @38
    @36
    cH
    cK
    cW
    @53
    @54
    lhp2lt.h
    lhp1cvr
    syl2anc
    eqbrtrd
    @15
    @38
    cK
    c.le
    @28
    @36
    @10
    @22
    lhp2lt.l
    @54
    cvrcmp
    syl132anc
    mpbid
    @57
    @29
    @28
    @37
    @38
    wbr
    #
    @26
    @29
    @34
    @55
    @9
    simpr2r
    @57
    @0
    @45
    @33
    @29
    @72
    wb
    @62
    @65
    @32
    @33
    @30
    @55
    @9
    simpr1r
    cA
    @15
    @38
    @27
    c.or
    cK
    c.le
    @28
    @22
    lhp2lt.l
    lhp2lt.j
    @54
    lhp2lt.a
    cvr1
    syl3anc
    mpbid
    eqbrtrrd
    3exp2
    3imp
    necon3bd
    mpd
    3exp
    rexlimdvv
    mpd
    @9
    @0
    @48
    @1
    @11
    @12
    @13
    wa
    wb
    @19
    @9
    @0
    @3
    @6
    @48
    @19
    @21
    @23
    @50
    syl3anc
    @24
    chlt
    @15
    cH
    c.lt
    cK
    c.le
    @10
    cW
    lhp2lt.l
    lhp2lt.s
    pltval
    syl3anc
    mpbir2and
end
