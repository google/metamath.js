include "wbr.mm"
include "chpg.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "hpgbr.mm"
include "mpbird.mm"
include "co.mm"
include "chlg.mm"
include "cds.mm"
include "eqid.mm"
include "crn.mm"
include "ad7antr.mm"
include "ad3antrrr.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "ad10antr.mm"
include "wne.mm"
include "wo.mm"
include "w3a.mm"
include "simplr.mm"
include "tglnpt.mm"
include "wn.mm"
include "simp-5r.mm"
include "oppne1.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "tgelrnln.mm"
include "tglinerflx2.mm"
include "nelne1.mm"
include "necomd.mm"
include "simpllr.mm"
include "simplrr.mm"
include "btwnlng1.mm"
include "elind.mm"
include "tglinerflx1.mm"
include "tglineineq.mm"
include "eqnetrd.mm"
include "simp-4r.mm"
include "simp-7r.mm"
include "simprr.mm"
include "simplrl.mm"
include "simprl.mm"
include "oppne2.mm"
include "tgbtwncom.mm"
include "eqeltrd.mm"
include "tgbtwnconn2.mm"
include "3jca.mm"
include "ishlg.mm"
include "opphl.mm"
include "tgbtwnne.mm"
include "btwnhl1.mm"
include "hlcomd.mm"
include "pm2.61dan.mm"
include "axtgpasch.mm"
include "r19.29a.mm"
include "islnopp.mm"
include "mpbid.mm"
include "simprd.mm"
include "eleq1.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "biimpa.mm"
include "impbida.mm"

theorem lnopp2hpgb
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ishpg.p: |- P = ( Base ` G )
  assume ishpg.i: |- I = ( Itv ` G )
  assume ishpg.l: |- L = ( LineG ` G )
  assume ishpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume ishpg.g: |- ( ph -> G e. TarskiG )
  assume ishpg.d: |- ( ph -> D e. ran L )
  assume hpgbr.a: |- ( ph -> A e. P )
  assume hpgbr.b: |- ( ph -> B e. P )
  assume lnopp2hpgb.c: |- ( ph -> C e. P )
  assume lnopp2hpgb.1: |- ( ph -> A O C )

  disjoint A t
  disjoint B t
  disjoint C a
  disjoint C b
  disjoint C t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint L a
  disjoint L b
  disjoint L t
  disjoint O a
  disjoint O b
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint ph t
  disjoint A d
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint d t
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C d
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint D d
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint G d
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I d
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint L d
  disjoint O d
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint P d
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint d ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( B O C <-> A ( ( hpG ` G ) ` D ) B ) )

  proof
    wph
    cB
    cC
    cO
    wbr
    #
    cA
    cB
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    #
    wph
    @0
    wa
    #
    @1
    cA
    vd
    cv
    #
    cO
    wbr
    #
    cB
    @3
    cO
    wbr
    #
    wa
    #
    vd
    cP
    wrex
    #
    @2
    cC
    cP
    wcel
    #
    cA
    cC
    cO
    wbr
    #
    @0
    @7
    wph
    @8
    @0
    lnopp2hpgb.c
    adantr
    wph
    @9
    @0
    lnopp2hpgb.1
    adantr
    wph
    @0
    simpr
    @6
    @9
    @0
    wa
    vd
    cC
    cP
    @3
    cC
    wceq
    @4
    @9
    @5
    @0
    @3
    cC
    cA
    cO
    breq2
    @3
    cC
    cB
    cO
    breq2
    anbi12d
    rspcev
    syl12anc
    wph
    @1
    @7
    wb
    @0
    wph
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    vd
    ishpg.p
    ishpg.i
    ishpg.l
    ishpg.o
    ishpg.g
    ishpg.d
    hpgbr.a
    hpgbr.b
    hpgbr
    #
    adantr
    mpbird
    wph
    @1
    wa
    #
    @6
    @0
    vd
    cP
    @11
    @3
    cP
    wcel
    #
    wa
    #
    @6
    wa
    #
    vx
    cv
    #
    cA
    @3
    cI
    co
    #
    wcel
    #
    @0
    vx
    cD
    @14
    @15
    cD
    wcel
    #
    wa
    #
    @17
    wa
    #
    vy
    cv
    #
    cB
    @3
    cI
    co
    #
    wcel
    #
    @0
    vy
    cD
    @20
    @21
    cD
    wcel
    #
    wa
    #
    @23
    wa
    #
    vz
    cv
    #
    @15
    cB
    cI
    co
    wcel
    #
    @27
    @21
    cA
    cI
    co
    wcel
    #
    wa
    #
    @0
    vz
    cP
    @26
    @27
    cP
    wcel
    #
    wa
    #
    @30
    wa
    #
    @27
    cD
    wcel
    #
    @0
    @33
    @34
    wa
    #
    vt
    cA
    cB
    cC
    cD
    cP
    @27
    cG
    cI
    cG
    chlg
    cfv
    #
    cL
    cG
    cds
    cfv
    #
    cO
    va
    vb
    ishpg.p
    @37
    eqid
    #
    ishpg.i
    ishpg.o
    ishpg.l
    @26
    cD
    cL
    crn
    wcel
    #
    @31
    @30
    @34
    wph
    @39
    @1
    @12
    @6
    @18
    @17
    @24
    @23
    ishpg.d
    ad7antr
    #
    ad3antrrr
    #
    @26
    cG
    cstrkg
    wcel
    #
    @31
    @30
    @34
    wph
    @42
    @1
    @12
    @6
    @18
    @17
    @24
    @23
    ishpg.g
    ad7antr
    #
    ad3antrrr
    #
    @36
    eqid
    #
    @26
    cA
    cP
    wcel
    #
    @31
    @30
    @34
    @14
    @46
    @18
    @17
    @24
    @23
    wph
    @46
    @1
    @12
    @6
    hpgbr.a
    ad3antrrr
    #
    ad4antr
    #
    ad3antrrr
    #
    @26
    cB
    cP
    wcel
    #
    @31
    @30
    @34
    @14
    @50
    @18
    @17
    @24
    @23
    wph
    @50
    @1
    @12
    @6
    hpgbr.b
    ad3antrrr
    #
    ad4antr
    #
    ad3antrrr
    #
    wph
    @8
    @1
    @12
    @6
    @18
    @17
    @24
    @23
    @31
    @30
    @34
    lnopp2hpgb.c
    ad10antr
    #
    wph
    @9
    @1
    @12
    @6
    @18
    @17
    @24
    @23
    @31
    @30
    @34
    lnopp2hpgb.1
    ad10antr
    #
    @33
    @34
    simpr
    #
    @35
    cA
    cB
    @27
    @36
    cfv
    wbr
    cA
    @27
    wne
    #
    cB
    @27
    wne
    #
    cA
    @27
    cB
    cI
    co
    wcel
    cB
    @27
    cA
    cI
    co
    wcel
    wo
    #
    w3a
    @35
    @57
    @58
    @59
    @35
    @27
    cA
    @35
    @27
    @21
    cA
    @35
    cD
    @21
    cA
    cL
    co
    #
    cP
    cG
    cI
    cL
    @27
    @21
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @41
    @35
    cP
    cG
    cI
    cL
    @21
    cA
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @26
    @21
    cP
    wcel
    #
    @31
    @30
    @34
    @26
    cD
    cP
    cG
    cI
    cL
    @21
    ishpg.p
    ishpg.l
    ishpg.i
    @43
    @40
    @20
    @24
    @23
    simplr
    #
    tglnpt
    #
    ad3antrrr
    #
    @49
    @35
    @24
    cA
    cD
    wcel
    wn
    #
    @21
    cA
    wne
    @20
    @24
    @23
    @31
    @30
    @34
    simp-5r
    #
    @35
    vt
    cA
    cC
    cD
    cP
    cG
    cI
    cL
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    ishpg.l
    @41
    @44
    @49
    @54
    @55
    oppne1
    #
    @21
    cA
    cD
    nelne2
    syl2anc
    #
    tgelrnln
    @35
    @60
    cD
    @35
    cA
    @60
    wcel
    @65
    @60
    cD
    wne
    @35
    cP
    @21
    cA
    cG
    cI
    cL
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @64
    @49
    @68
    tglinerflx2
    @67
    cA
    @60
    cD
    nelne1
    syl2anc
    necomd
    @35
    cD
    @60
    @27
    @56
    @35
    cP
    cG
    cI
    cL
    @21
    cA
    @27
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @64
    @49
    @26
    @31
    @30
    @34
    simpllr
    #
    @68
    @32
    @28
    @29
    @34
    simplrr
    btwnlng1
    elind
    @35
    cD
    @60
    @21
    @66
    @35
    cP
    @21
    cA
    cG
    cI
    cL
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @64
    @49
    @68
    tglinerflx1
    elind
    tglineineq
    #
    @68
    eqnetrd
    necomd
    @35
    @27
    cB
    @35
    @27
    @15
    cB
    @35
    cD
    @15
    cB
    cL
    co
    #
    cP
    cG
    cI
    cL
    @27
    @15
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @41
    @35
    cP
    cG
    cI
    cL
    @15
    cB
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @26
    @15
    cP
    wcel
    #
    @31
    @30
    @34
    @26
    cD
    cP
    cG
    cI
    cL
    @15
    ishpg.p
    ishpg.l
    ishpg.i
    @43
    @40
    @14
    @18
    @17
    @24
    @23
    simp-4r
    #
    tglnpt
    #
    ad3antrrr
    #
    @53
    @35
    @18
    cB
    cD
    wcel
    wn
    #
    @15
    cB
    wne
    @14
    @18
    @17
    @24
    @23
    @31
    @30
    @34
    simp-7r
    #
    @35
    vt
    cB
    @3
    cD
    cP
    cG
    cI
    cL
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    ishpg.l
    @41
    @44
    @53
    @26
    @12
    @31
    @30
    @34
    @14
    @12
    @18
    @17
    @24
    @23
    @11
    @12
    @6
    simplr
    #
    ad4antr
    #
    ad3antrrr
    #
    @14
    @5
    @18
    @17
    @24
    @23
    @31
    @30
    @34
    @13
    @4
    @5
    simprr
    #
    ad7antr
    oppne1
    #
    @15
    cB
    cD
    nelne2
    syl2anc
    #
    tgelrnln
    @35
    @71
    cD
    @35
    cB
    @71
    wcel
    @76
    @71
    cD
    wne
    @35
    cP
    @15
    cB
    cG
    cI
    cL
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @75
    @53
    @83
    tglinerflx2
    @82
    cB
    @71
    cD
    nelne1
    syl2anc
    necomd
    @35
    cD
    @71
    @27
    @56
    @35
    cP
    cG
    cI
    cL
    @15
    cB
    @27
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @75
    @53
    @69
    @83
    @32
    @28
    @29
    @34
    simplrl
    btwnlng1
    elind
    @35
    cD
    @71
    @15
    @77
    @35
    cP
    @15
    cB
    cG
    cI
    cL
    ishpg.p
    ishpg.i
    ishpg.l
    @44
    @75
    @53
    @83
    tglinerflx1
    elind
    tglineineq
    #
    @83
    eqnetrd
    necomd
    @35
    @3
    @27
    cA
    cB
    cP
    cG
    cI
    ishpg.p
    ishpg.i
    @44
    @80
    @69
    @49
    @53
    @35
    @27
    @3
    @35
    @34
    @3
    cD
    wcel
    wn
    #
    @27
    @3
    wne
    @56
    @35
    vt
    cA
    @3
    cD
    cP
    cG
    cI
    cL
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    ishpg.l
    @41
    @44
    @49
    @80
    @14
    @4
    @18
    @17
    @24
    @23
    @31
    @30
    @34
    @13
    @4
    @5
    simprl
    #
    ad7antr
    oppne2
    @27
    @3
    cD
    nelne2
    syl2anc
    necomd
    @35
    @27
    @15
    @3
    cA
    cI
    co
    @84
    @35
    cA
    @15
    @3
    cP
    cG
    cI
    @37
    ishpg.p
    @38
    ishpg.i
    @44
    @49
    @75
    @80
    @26
    @17
    @31
    @30
    @34
    @19
    @17
    @24
    @23
    simpllr
    #
    ad3antrrr
    tgbtwncom
    eqeltrd
    @35
    @27
    @21
    @3
    cB
    cI
    co
    @70
    @35
    cB
    @21
    @3
    cP
    cG
    cI
    @37
    ishpg.p
    @38
    ishpg.i
    @44
    @53
    @64
    @80
    @26
    @23
    @31
    @30
    @34
    @25
    @23
    simpr
    #
    ad3antrrr
    tgbtwncom
    eqeltrd
    tgbtwnconn2
    3jca
    @35
    cA
    cB
    @27
    cP
    cG
    cI
    @36
    cstrkg
    ishpg.p
    ishpg.i
    @45
    @49
    @53
    @69
    @44
    ishlg
    mpbird
    opphl
    @33
    @34
    wn
    #
    wa
    #
    vt
    @27
    cB
    cC
    cD
    cP
    @15
    cG
    cI
    @36
    cL
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    ishpg.l
    @26
    @39
    @31
    @30
    @89
    @40
    ad3antrrr
    #
    @26
    @42
    @31
    @30
    @89
    @43
    ad3antrrr
    #
    @45
    @26
    @31
    @30
    @89
    simpllr
    #
    @26
    @50
    @31
    @30
    @89
    @52
    ad3antrrr
    #
    wph
    @8
    @1
    @12
    @6
    @18
    @17
    @24
    @23
    @31
    @30
    @89
    lnopp2hpgb.c
    ad10antr
    #
    @90
    vt
    cA
    @27
    cC
    cD
    cP
    @21
    cG
    cI
    @36
    cL
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    ishpg.l
    @91
    @92
    @45
    @26
    @46
    @31
    @30
    @89
    @48
    ad3antrrr
    #
    @93
    @95
    wph
    @9
    @1
    @12
    @6
    @18
    @17
    @24
    @23
    @31
    @30
    @89
    lnopp2hpgb.1
    ad10antr
    @26
    @24
    @31
    @30
    @89
    @62
    ad3antrrr
    #
    @90
    @27
    cA
    @21
    cP
    cG
    cI
    @36
    cstrkg
    ishpg.p
    ishpg.i
    @45
    @93
    @96
    @26
    @61
    @31
    @30
    @89
    @63
    ad3antrrr
    #
    @92
    @90
    @21
    cA
    @27
    cA
    cP
    cG
    cI
    @36
    ishpg.p
    ishpg.i
    @45
    @98
    @96
    @93
    @92
    @96
    @32
    @28
    @29
    @89
    simplrr
    #
    @90
    @21
    @27
    cA
    cP
    cG
    cI
    @37
    ishpg.p
    @38
    ishpg.i
    @92
    @98
    @93
    @96
    @99
    @90
    @21
    @27
    @90
    @24
    @89
    @21
    @27
    wne
    @97
    @33
    @89
    simpr
    #
    @21
    @27
    cD
    nelne2
    syl2anc
    necomd
    #
    tgbtwnne
    @101
    btwnhl1
    hlcomd
    opphl
    @26
    @18
    @31
    @30
    @89
    @73
    ad3antrrr
    #
    @90
    @15
    cB
    @27
    cA
    cP
    cG
    cI
    @36
    ishpg.p
    ishpg.i
    @45
    @26
    @72
    @31
    @30
    @89
    @74
    ad3antrrr
    #
    @94
    @93
    @92
    @96
    @32
    @28
    @29
    @89
    simplrl
    #
    @90
    @15
    @27
    cB
    cP
    cG
    cI
    @37
    ishpg.p
    @38
    ishpg.i
    @92
    @103
    @93
    @94
    @104
    @90
    @15
    @27
    @90
    @18
    @89
    @15
    @27
    wne
    @102
    @100
    @15
    @27
    cD
    nelne2
    syl2anc
    necomd
    #
    tgbtwnne
    @105
    btwnhl1
    opphl
    pm2.61dan
    @26
    cP
    @15
    cG
    cI
    @37
    @21
    cA
    cB
    @3
    vz
    ishpg.p
    @38
    ishpg.i
    @43
    @48
    @52
    @79
    @74
    @63
    @87
    @88
    axtgpasch
    r19.29a
    @14
    @23
    vy
    cD
    wrex
    #
    @18
    @17
    @14
    vt
    cv
    #
    @22
    wcel
    #
    vt
    cD
    wrex
    #
    @106
    @14
    @76
    @85
    wa
    #
    @109
    @14
    @5
    @110
    @109
    wa
    @81
    @14
    vt
    cB
    @3
    cD
    cP
    cG
    cI
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    @51
    @78
    islnopp
    mpbid
    simprd
    @108
    @23
    vt
    vy
    cD
    @107
    @21
    @22
    eleq1
    cbvrexv
    sylib
    ad2antrr
    r19.29a
    @14
    @107
    @16
    wcel
    #
    vt
    cD
    wrex
    #
    @17
    vx
    cD
    wrex
    @14
    @65
    @85
    wa
    #
    @112
    @14
    @4
    @113
    @112
    wa
    @86
    @14
    vt
    cA
    @3
    cD
    cP
    cG
    cI
    @37
    cO
    va
    vb
    ishpg.p
    @38
    ishpg.i
    ishpg.o
    @47
    @78
    islnopp
    mpbid
    simprd
    @111
    @17
    vt
    vx
    cD
    @107
    @15
    @16
    eleq1
    cbvrexv
    sylib
    r19.29a
    wph
    @1
    @7
    @10
    biimpa
    r19.29a
    impbida
end
