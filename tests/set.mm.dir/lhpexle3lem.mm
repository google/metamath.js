include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "wceq.mm"
include "simpl1.mm"
include "lhpexle2.mm"
include "syl.mm"
include "simp31.mm"
include "simp32.mm"
include "simp1r.mm"
include "neeqtrd.mm"
include "simp33.mm"
include "3jca.mm"
include "jca.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "wn.mm"
include "simprrr.mm"
include "clat.mm"
include "cbs.mm"
include "simp11l.mm"
include "adantr.mm"
include "hllat.mm"
include "eqid.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "simp121.mm"
include "simp122.mm"
include "simprrl.mm"
include "latnlej1l.mm"
include "syl131anc.mm"
include "latnlej1r.mm"
include "simpl3.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "cplt.mm"
include "simp11.mm"
include "simp131.mm"
include "simp132.mm"
include "lhp2lt.mm"
include "syl122anc.mm"
include "wi.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "hlrelat1.mm"
include "reximddv.mm"
include "3expa.mm"
include "simprr3.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"
include "simprr1.mm"
include "simprr2.mm"
include "simp2.mm"
include "hlsupr.mm"
include "syl31anc.mm"
include "pm2.61dan.mm"
include "pm2.61dane.mm"

theorem lhpexle3lem
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  assume lhpex1.l: |- .<_ = ( le ` K )
  assume lhpex1.a: |- A = ( Atoms ` K )
  assume lhpex1.h: |- H = ( LHyp ` K )

  disjoint .<_ p
  disjoint A p
  disjoint H p
  disjoint K p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. A /\ Y e. A /\ Z e. A ) /\ ( X .<_ W /\ Y .<_ W /\ Z .<_ W ) ) -> E. p e. A ( p .<_ W /\ ( p =/= X /\ p =/= Y /\ p =/= Z ) ) )

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
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    cZ
    cA
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
    cZ
    cW
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    @12
    cX
    wne
    #
    @12
    cY
    wne
    #
    @12
    cZ
    wne
    #
    w3a
    #
    wa
    #
    vp
    cA
    wrex
    #
    cX
    cY
    @11
    cX
    cY
    wceq
    #
    wa
    #
    @13
    @14
    @16
    w3a
    #
    vp
    cA
    wrex
    #
    @19
    @21
    @2
    @23
    @2
    @6
    @10
    @20
    simpl1
    cA
    cH
    cK
    c.le
    cW
    cX
    cZ
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle2
    syl
    @21
    @22
    @18
    vp
    cA
    @21
    @12
    cA
    wcel
    #
    @22
    @18
    @21
    @24
    @22
    w3a
    #
    @13
    @17
    @21
    @24
    @13
    @14
    @16
    simp31
    @25
    @14
    @15
    @16
    @21
    @24
    @13
    @14
    @16
    simp32
    #
    @25
    @12
    cX
    cY
    @26
    @11
    @20
    @24
    @22
    simp1r
    neeqtrd
    @21
    @24
    @13
    @14
    @16
    simp33
    3jca
    jca
    3exp
    reximdvai
    mpd
    @11
    cX
    cY
    wne
    #
    wa
    cZ
    cX
    cY
    cK
    cjn
    cfv
    #
    co
    #
    c.le
    wbr
    #
    @19
    @11
    @27
    @30
    @19
    @11
    @27
    @30
    w3a
    #
    @12
    @29
    c.le
    wbr
    #
    wn
    #
    @13
    wa
    #
    @18
    vp
    cA
    @31
    @24
    @34
    wa
    #
    wa
    #
    @13
    @17
    @31
    @24
    @33
    @13
    simprrr
    @36
    @14
    @15
    @16
    @36
    cK
    clat
    wcel
    #
    @12
    cK
    cbs
    cfv
    #
    wcel
    #
    cX
    @38
    wcel
    #
    cY
    @38
    wcel
    #
    @33
    @14
    @36
    @0
    @37
    @31
    @0
    @35
    @0
    @1
    @6
    @10
    @27
    @30
    simp11l
    #
    adantr
    cK
    hllat
    #
    syl
    #
    @24
    @39
    @31
    @34
    cA
    @38
    @12
    cK
    @38
    eqid
    #
    lhpex1.a
    atbase
    #
    ad2antrl
    #
    @36
    @3
    @40
    @31
    @3
    @35
    @3
    @4
    @5
    @2
    @10
    @27
    @30
    simp121
    #
    adantr
    cA
    @38
    cX
    cK
    @45
    lhpex1.a
    atbase
    #
    syl
    #
    @36
    @4
    @41
    @31
    @4
    @35
    @3
    @4
    @5
    @2
    @10
    @27
    @30
    simp122
    #
    adantr
    cA
    @38
    cY
    cK
    @45
    lhpex1.a
    atbase
    #
    syl
    #
    @31
    @24
    @33
    @13
    simprrl
    #
    @38
    @28
    cK
    c.le
    @12
    cX
    cY
    @45
    lhpex1.l
    @28
    eqid
    #
    latnlej1l
    syl131anc
    @36
    @37
    @39
    @40
    @41
    @33
    @15
    @44
    @47
    @50
    @53
    @54
    @38
    @28
    cK
    c.le
    @12
    cX
    cY
    @45
    lhpex1.l
    @55
    latnlej1r
    syl131anc
    @36
    @30
    @33
    @16
    @11
    @27
    @30
    @35
    simpl3
    @54
    @30
    @33
    wa
    cZ
    @12
    cZ
    @12
    @29
    c.le
    nbrne2
    necomd
    syl2anc
    3jca
    jca
    @31
    @29
    cW
    cK
    cplt
    cfv
    #
    wbr
    #
    @34
    vp
    cA
    wrex
    #
    @31
    @2
    @3
    @7
    @4
    @8
    @57
    @2
    @6
    @10
    @27
    @30
    simp11
    @48
    @7
    @8
    @9
    @2
    @6
    @27
    @30
    simp131
    @51
    @7
    @8
    @9
    @2
    @6
    @27
    @30
    simp132
    cA
    cX
    cY
    @56
    cH
    @28
    cK
    c.le
    cW
    lhpex1.l
    @56
    eqid
    #
    @55
    lhpex1.a
    lhpex1.h
    lhp2lt
    syl122anc
    @31
    @0
    @29
    @38
    wcel
    #
    cW
    @38
    wcel
    #
    @57
    @58
    wi
    @42
    @31
    @0
    @3
    @4
    @60
    @42
    @48
    @51
    cA
    @38
    @28
    cK
    cX
    cY
    @45
    @55
    lhpex1.a
    hlatjcl
    #
    syl3anc
    @31
    @1
    @61
    @0
    @1
    @6
    @10
    @27
    @30
    simp11r
    @38
    cH
    cK
    cW
    @45
    lhpex1.h
    lhpbase
    #
    syl
    cA
    @38
    @56
    cK
    c.le
    @29
    cW
    vp
    @45
    lhpex1.l
    @59
    lhpex1.a
    hlrelat1
    syl3anc
    mpd
    reximddv
    3expa
    @11
    @27
    @30
    wn
    #
    @19
    @11
    @27
    @64
    w3a
    #
    @14
    @15
    @32
    w3a
    #
    @18
    vp
    cA
    @65
    @24
    @66
    wa
    #
    wa
    #
    @13
    @17
    @68
    @38
    cK
    c.le
    @12
    @29
    cW
    @45
    lhpex1.l
    @68
    @0
    @37
    @65
    @0
    @67
    @0
    @1
    @6
    @10
    @27
    @64
    simp11l
    #
    adantr
    #
    @43
    syl
    #
    @24
    @39
    @65
    @66
    @46
    ad2antrl
    @68
    @0
    @3
    @4
    @60
    @70
    @65
    @3
    @67
    @3
    @4
    @5
    @2
    @10
    @27
    @64
    simp121
    #
    adantr
    #
    @65
    @4
    @67
    @3
    @4
    @5
    @2
    @10
    @27
    @64
    simp122
    #
    adantr
    #
    @62
    syl3anc
    @68
    @1
    @61
    @65
    @1
    @67
    @0
    @1
    @6
    @10
    @27
    @64
    simp11r
    adantr
    @63
    syl
    #
    @14
    @15
    @32
    @24
    @65
    simprr3
    #
    @68
    @7
    @8
    @29
    cW
    c.le
    wbr
    #
    @65
    @7
    @67
    @7
    @8
    @9
    @2
    @6
    @27
    @64
    simp131
    adantr
    @65
    @8
    @67
    @7
    @8
    @9
    @2
    @6
    @27
    @64
    simp132
    adantr
    @68
    @37
    @40
    @41
    @61
    @7
    @8
    wa
    @78
    wb
    @71
    @68
    @3
    @40
    @73
    @49
    syl
    @68
    @4
    @41
    @75
    @52
    syl
    @76
    @38
    @28
    cK
    c.le
    cX
    cY
    cW
    @45
    lhpex1.l
    @55
    latjle12
    syl13anc
    mpbi2and
    lattrd
    @68
    @14
    @15
    @16
    @14
    @15
    @32
    @24
    @65
    simprr1
    @14
    @15
    @32
    @24
    @65
    simprr2
    @68
    @32
    @64
    @16
    @77
    @11
    @27
    @64
    @67
    simpl3
    @12
    cZ
    @29
    c.le
    nbrne2
    syl2anc
    3jca
    jca
    @65
    @0
    @3
    @4
    @27
    @66
    vp
    cA
    wrex
    @69
    @72
    @74
    @11
    @27
    @64
    simp2
    cA
    cX
    cY
    @28
    cK
    c.le
    vp
    lhpex1.l
    @55
    lhpex1.a
    hlsupr
    syl31anc
    reximddv
    3expa
    pm2.61dan
    pm2.61dane
end
