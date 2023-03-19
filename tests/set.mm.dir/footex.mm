include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wrex.mm"
include "wcel.mm"
include "cmir.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "ad6antr.mm"
include "simplr.mm"
include "simp-4r.mm"
include "simprr.mm"
include "eqcomd.mm"
include "midexlem.mm"
include "adantr.mm"
include "simp-6r.mm"
include "simprl.mm"
include "ad4antr.mm"
include "simp-5r.mm"
include "simprd.mm"
include "simp-7r.mm"
include "wn.mm"
include "simpllr.mm"
include "ad10antr.mm"
include "simp-11r.mm"
include "necomd.mm"
include "simp-9r.mm"
include "simpld.mm"
include "btwnlng3.mm"
include "lncom.mm"
include "eleqtrrd.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "eqnetrrd.mm"
include "mirinv.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "tgcgrneq.mm"
include "mircl.mm"
include "mirbtwn.mm"
include "oveq1d.mm"
include "tgbtwnouttr2.mm"
include "tgbtwncom.mm"
include "simplrl.mm"
include "cs3.mm"
include "crag.mm"
include "ccgrg.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "israg.mm"
include "mpbird.mm"
include "tgcgrcomlr.mm"
include "eqtr2d.mm"
include "tglinerflx1.mm"
include "axtgcgrrflx.mm"
include "axtg5seg.mm"
include "trgcgr.mm"
include "ragcgr.mm"
include "ragcom.mm"
include "eqidd.mm"
include "krippen.mm"
include "crn.mm"
include "ad5antr.mm"
include "ad9antr.mm"
include "tglinethru.mm"
include "tgelrnln.mm"
include "tglinerflx2.mm"
include "elind.mm"
include "simpr.mm"
include "s3eqd.mm"
include "mircgr.mm"
include "neeqtrd.mm"
include "eleqtrd.mm"
include "orcd.mm"
include "ragcol.mm"
include "eqeltrd.mm"
include "wo.mm"
include "btwncolg3.mm"
include "ragflat.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "ragperp.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "axtgsegcon.mm"
include "r19.29a.mm"
include "tgisline.mm"
include "r19.29vva.mm"

theorem footex
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume foot.x: |- ( ph -> C e. P )
  assume foot.y: |- ( ph -> -. C e. A )

  disjoint A x
  disjoint C x
  disjoint G x
  disjoint I x
  disjoint .- x
  disjoint L x
  disjoint P x
  disjoint ph x
  disjoint A x
  disjoint G x
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint A d
  disjoint A p
  disjoint A q
  disjoint A u
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint a b
  disjoint a d
  disjoint a p
  disjoint a q
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b d
  disjoint b p
  disjoint b q
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint d p
  disjoint d q
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C a
  disjoint C b
  disjoint C d
  disjoint C p
  disjoint C q
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint G a
  disjoint G b
  disjoint G d
  disjoint G p
  disjoint G q
  disjoint G y
  disjoint G z
  disjoint I a
  disjoint I b
  disjoint I d
  disjoint I p
  disjoint I q
  disjoint I y
  disjoint I z
  disjoint .- d
  disjoint .- p
  disjoint .- q
  disjoint .- y
  disjoint .- z
  disjoint L a
  disjoint L b
  disjoint L d
  disjoint L p
  disjoint L q
  disjoint L u
  disjoint L v
  disjoint L y
  disjoint L z
  disjoint P a
  disjoint P b
  disjoint P d
  disjoint P p
  disjoint P q
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint p ph
  disjoint ph q
  disjoint ph y
  disjoint ph z
  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint A b
  disjoint u v
  disjoint u x
  disjoint A u
  disjoint v x
  disjoint A v
  disjoint B a
  disjoint B b
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint a g
  disjoint G a
  disjoint b g
  disjoint G b
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint G g
  disjoint G u
  disjoint G v
  disjoint L a
  disjoint L b
  disjoint L g
  disjoint a ph
  disjoint b ph
  disjoint g ph
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> E. x e. A ( C L x ) ( perpG ` G ) A )

  proof
    wph
    cA
    va
    cv
    #
    vb
    cv
    #
    cL
    co
    #
    wceq
    #
    @0
    @1
    wne
    #
    wa
    #
    cC
    vx
    cv
    #
    cL
    co
    #
    cA
    cG
    cperpg
    cfv
    wbr
    #
    vx
    cA
    wrex
    #
    va
    vb
    cP
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @1
    cP
    wcel
    #
    wa
    #
    @5
    wa
    #
    @0
    @1
    vy
    cv
    #
    cI
    co
    wcel
    #
    @0
    @15
    c.mi
    co
    #
    @0
    cC
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @9
    vy
    cP
    @14
    @15
    cP
    wcel
    #
    wa
    #
    @20
    wa
    #
    cC
    @15
    vp
    cv
    #
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    @9
    vp
    cP
    @23
    @24
    cP
    wcel
    #
    wa
    #
    @28
    wa
    #
    @15
    @0
    vz
    cv
    #
    cI
    co
    wcel
    #
    @15
    @32
    c.mi
    co
    #
    @15
    @24
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @9
    vz
    cP
    @31
    @32
    cP
    wcel
    #
    wa
    #
    @37
    wa
    #
    @15
    @24
    vq
    cv
    #
    cI
    co
    wcel
    #
    @15
    @41
    c.mi
    co
    #
    @15
    @0
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @9
    vq
    cP
    @40
    @41
    cP
    wcel
    #
    wa
    #
    @46
    wa
    #
    @15
    @41
    @32
    @25
    cfv
    #
    cfv
    #
    vd
    cv
    #
    cI
    co
    wcel
    #
    @15
    @52
    c.mi
    co
    #
    @15
    cC
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @9
    vd
    cP
    @49
    @52
    cP
    wcel
    #
    wa
    #
    @57
    wa
    #
    @52
    cC
    @6
    @25
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    cP
    wrex
    @9
    @60
    vx
    cC
    @52
    @15
    cP
    @25
    cG
    cI
    cL
    @61
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @25
    eqid
    #
    @49
    cG
    cstrkg
    wcel
    #
    @58
    @57
    @40
    @65
    @47
    @46
    @31
    @65
    @38
    @37
    @23
    @65
    @29
    @28
    @14
    @65
    @21
    @20
    wph
    @65
    @10
    @12
    @5
    isperp.g
    ad3antrrr
    #
    ad2antrr
    #
    ad2antrr
    #
    ad2antrr
    #
    ad2antrr
    #
    ad2antrr
    #
    @61
    eqid
    #
    @49
    cC
    cP
    wcel
    #
    @58
    @57
    @23
    @73
    @29
    @28
    @38
    @37
    @47
    @46
    @14
    @73
    @21
    @20
    wph
    @73
    @10
    @12
    @5
    foot.x
    ad3antrrr
    #
    ad2antrr
    #
    ad6antr
    #
    ad2antrr
    #
    @49
    @58
    @57
    simplr
    @49
    @21
    @58
    @57
    @40
    @21
    @47
    @46
    @31
    @21
    @38
    @37
    @14
    @21
    @20
    @29
    @28
    simp-4r
    #
    ad2antrr
    #
    ad2antrr
    #
    ad2antrr
    #
    @60
    @54
    @55
    @59
    @53
    @56
    simprr
    eqcomd
    #
    midexlem
    @60
    @63
    @8
    vx
    cP
    cA
    @60
    @6
    cP
    wcel
    #
    @63
    wa
    #
    @6
    cA
    wcel
    #
    @8
    wa
    @60
    @84
    wa
    #
    @85
    @8
    @86
    @6
    @15
    @32
    cL
    co
    cA
    @86
    cP
    cG
    cI
    cL
    @15
    @32
    @6
    isperp.p
    isperp.i
    isperp.l
    @60
    @65
    @84
    @71
    adantr
    #
    @60
    @21
    @84
    @81
    adantr
    #
    @60
    @38
    @84
    @31
    @38
    @37
    @47
    @46
    @58
    @57
    simp-6r
    #
    adantr
    #
    @60
    @83
    @63
    simprl
    #
    @86
    @15
    @24
    @15
    @32
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @88
    @60
    @29
    @84
    @40
    @29
    @47
    @46
    @58
    @57
    @23
    @29
    @28
    @38
    @37
    simp-4r
    #
    ad4antr
    #
    adantr
    #
    @88
    @90
    @60
    @35
    @34
    wceq
    @84
    @60
    @34
    @35
    @60
    @33
    @36
    @39
    @37
    @47
    @46
    @58
    @57
    simp-5r
    #
    simprd
    eqcomd
    #
    adantr
    @86
    @24
    @15
    @86
    @27
    @15
    wne
    @24
    @15
    wne
    @86
    cC
    @27
    @15
    @60
    @28
    @84
    @30
    @28
    @38
    @37
    @47
    @46
    @58
    @57
    simp-7r
    #
    adantr
    #
    @86
    @15
    cC
    @86
    @15
    cA
    wcel
    #
    cC
    cA
    wcel
    wn
    #
    @15
    cC
    wne
    @60
    @99
    @84
    @60
    @15
    @2
    cA
    @60
    cP
    cG
    cI
    cL
    @0
    @1
    @15
    isperp.p
    isperp.i
    isperp.l
    @71
    @40
    @10
    @47
    @46
    @58
    @57
    @31
    @10
    @38
    @37
    @23
    @10
    @29
    @28
    @14
    @10
    @21
    @20
    wph
    @10
    @12
    @5
    simpllr
    #
    ad2antrr
    #
    ad2antrr
    #
    ad2antrr
    #
    ad4antr
    #
    @14
    @12
    @21
    @20
    @29
    @28
    @38
    @37
    @47
    @46
    @58
    @57
    @11
    @12
    @5
    simplr
    #
    ad10antr
    #
    @81
    @60
    @3
    @4
    @13
    @5
    @21
    @20
    @29
    @28
    @38
    @37
    @47
    @46
    @58
    @57
    simp-11r
    #
    simprd
    #
    @60
    cP
    cG
    cI
    cL
    @1
    @0
    @15
    isperp.p
    isperp.i
    isperp.l
    @71
    @107
    @105
    @81
    @60
    @0
    @1
    @109
    necomd
    @60
    @16
    @19
    @22
    @20
    @29
    @28
    @38
    @37
    @47
    @46
    @58
    @57
    simp-9r
    #
    simpld
    btwnlng3
    lncom
    @60
    @3
    @4
    @108
    simpld
    #
    eleqtrrd
    adantr
    #
    @60
    @100
    @84
    @14
    @100
    @21
    @20
    @29
    @28
    @38
    @37
    @47
    @46
    @58
    @57
    wph
    @100
    @10
    @12
    @5
    foot.y
    ad3antrrr
    ad10antr
    #
    adantr
    #
    @15
    cC
    cA
    nelne2
    syl2anc
    necomd
    #
    eqnetrrd
    @86
    @27
    @15
    @24
    @15
    @86
    @24
    @15
    cP
    @25
    cG
    cI
    cL
    @26
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @94
    @26
    eqid
    #
    @88
    mirinv
    necon3bid
    mpbid
    #
    necomd
    #
    tgcgrneq
    #
    @86
    cP
    cG
    cI
    cL
    @32
    @15
    @6
    isperp.p
    isperp.i
    isperp.l
    @87
    @90
    @88
    @91
    @86
    @15
    @32
    @119
    necomd
    #
    @86
    @41
    @51
    @15
    cP
    @25
    cC
    @52
    cG
    cI
    cL
    @50
    c.mi
    @61
    @32
    @6
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @50
    eqid
    #
    @72
    @60
    @47
    @84
    @40
    @47
    @46
    @58
    @57
    simp-4r
    #
    adantr
    #
    @49
    @51
    cP
    wcel
    @58
    @57
    @84
    @49
    @32
    cP
    @25
    cG
    cI
    cL
    @50
    c.mi
    @41
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @70
    @31
    @38
    @37
    @47
    @46
    simp-4r
    @121
    @40
    @47
    @46
    simplr
    mircl
    #
    ad3antrrr
    #
    @88
    @60
    @73
    @84
    @77
    adantr
    #
    @49
    @58
    @57
    @84
    simpllr
    #
    @90
    @91
    @86
    cC
    @15
    @41
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @126
    @88
    @123
    @86
    cC
    @24
    @15
    @41
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @126
    @94
    @88
    @123
    @117
    @86
    @24
    @27
    @15
    cI
    co
    cC
    @15
    cI
    co
    @86
    @24
    @15
    cP
    @25
    cG
    cI
    cL
    @26
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @94
    @116
    @88
    mirbtwn
    @86
    cC
    @27
    @15
    cI
    @98
    oveq1d
    eleqtrrd
    #
    @60
    @42
    @84
    @60
    @42
    @45
    @48
    @46
    @58
    @57
    simpllr
    #
    simpld
    #
    adantr
    tgbtwnouttr2
    tgbtwncom
    #
    @59
    @53
    @56
    @84
    simplrl
    #
    @60
    @43
    @15
    @51
    c.mi
    co
    wceq
    #
    @84
    @60
    @15
    @32
    @41
    cs3
    cG
    crag
    cfv
    #
    wcel
    @133
    @60
    @41
    @32
    @15
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @71
    @122
    @89
    @81
    @60
    @0
    @24
    @15
    @41
    cP
    cG
    ccgrg
    cfv
    #
    @25
    @32
    @15
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @71
    @105
    @93
    @81
    @135
    eqid
    #
    @122
    @89
    @81
    @60
    @0
    @24
    @15
    cs3
    @134
    wcel
    #
    @17
    @0
    @27
    c.mi
    co
    #
    wceq
    @60
    @17
    @18
    @138
    @60
    @16
    @19
    @110
    simprd
    #
    @60
    cC
    @27
    @0
    c.mi
    @97
    oveq2d
    eqtrd
    @60
    @0
    @24
    @15
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @71
    @105
    @93
    @81
    israg
    mpbird
    #
    @60
    @0
    @24
    @15
    @41
    cP
    @135
    @32
    @15
    cG
    c.mi
    isperp.p
    isperp.d
    @136
    @71
    @105
    @93
    @81
    @122
    @89
    @81
    @60
    @24
    @0
    @32
    @41
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @71
    @93
    @105
    @89
    @122
    @60
    @0
    @15
    @32
    cP
    @0
    cG
    cI
    c.mi
    @41
    @41
    @15
    @24
    isperp.p
    isperp.d
    isperp.i
    @71
    @122
    @81
    @93
    @105
    @81
    @89
    @105
    @122
    @60
    @15
    @41
    @60
    cC
    @0
    @15
    @41
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @71
    @77
    @105
    @81
    @122
    @60
    @43
    @44
    cC
    @0
    c.mi
    co
    @60
    @42
    @45
    @129
    simprd
    #
    @60
    @0
    @15
    @0
    cC
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @71
    @105
    @81
    @105
    @77
    @139
    tgcgrcomlr
    eqtr2d
    @60
    @0
    cC
    @60
    @0
    cA
    wcel
    #
    @100
    @0
    cC
    wne
    #
    @60
    @0
    @2
    cA
    @60
    cP
    @0
    @1
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @71
    @105
    @107
    @109
    tglinerflx1
    @111
    eleqtrrd
    #
    @113
    @0
    cC
    cA
    nelne2
    syl2anc
    #
    necomd
    tgcgrneq
    necomd
    #
    @60
    @24
    @15
    @41
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @71
    @93
    @81
    @122
    @130
    tgbtwncom
    @60
    @33
    @36
    @95
    simpld
    #
    @60
    @15
    @41
    @15
    @0
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @71
    @81
    @122
    @81
    @105
    @141
    tgcgrcomlr
    @96
    @60
    cP
    cG
    cI
    c.mi
    @41
    @0
    isperp.p
    isperp.d
    isperp.i
    @71
    @122
    @105
    axtgcgrrflx
    @60
    @43
    @44
    @141
    eqcomd
    #
    axtg5seg
    tgcgrcomlr
    @60
    @15
    @24
    @15
    @32
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @71
    @81
    @93
    @81
    @89
    @96
    tgcgrcomlr
    @148
    trgcgr
    ragcgr
    ragcom
    @60
    @15
    @32
    @41
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @71
    @81
    @89
    @122
    israg
    mpbid
    adantr
    #
    @60
    @55
    @54
    wceq
    @84
    @82
    adantr
    #
    @86
    @51
    eqidd
    @60
    @83
    @63
    simprr
    #
    krippen
    btwnlng3
    lncom
    @86
    cA
    cP
    @15
    @32
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @87
    @88
    @90
    @119
    @119
    @23
    cA
    cL
    crn
    wcel
    #
    @29
    @28
    @38
    @37
    @47
    @46
    @58
    @57
    @84
    wph
    @152
    @10
    @12
    @5
    @21
    @20
    isperp.a
    ad5antr
    ad9antr
    #
    @112
    @86
    @32
    @0
    @15
    cL
    co
    #
    cA
    @86
    cP
    cG
    cI
    cL
    @0
    @15
    @32
    isperp.p
    isperp.i
    isperp.l
    @87
    @60
    @10
    @84
    @105
    adantr
    #
    @88
    @90
    @86
    @0
    cC
    @0
    @15
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @155
    @126
    @155
    @88
    @86
    @17
    @18
    @60
    @19
    @84
    @139
    adantr
    eqcomd
    #
    @60
    @143
    @84
    @145
    adantr
    #
    tgcgrneq
    #
    @60
    @33
    @84
    @147
    adantr
    btwnlng3
    #
    @86
    cA
    cP
    @0
    @15
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @87
    @155
    @88
    @158
    @158
    @153
    @60
    @142
    @84
    @144
    adantr
    @112
    tglinethru
    eleqtrrd
    tglinethru
    eleqtrrd
    #
    @86
    @7
    cA
    cP
    cC
    cG
    cI
    cL
    c.mi
    @15
    @6
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @87
    @86
    cP
    cG
    cI
    cL
    cC
    @6
    isperp.p
    isperp.i
    isperp.l
    @87
    @126
    @91
    @86
    @6
    cC
    @86
    @85
    @100
    @6
    cC
    wne
    @160
    @114
    @6
    cC
    cA
    nelne2
    syl2anc
    necomd
    #
    tgelrnln
    @153
    @86
    @7
    cA
    @6
    @86
    cP
    cC
    @6
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @87
    @126
    @91
    @161
    tglinerflx2
    @160
    elind
    @86
    cP
    cC
    @6
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @87
    @126
    @91
    @161
    tglinerflx1
    @112
    @161
    @86
    @15
    @6
    @86
    @15
    @6
    wceq
    #
    @15
    @24
    wceq
    #
    @86
    @162
    wa
    #
    @0
    @15
    @24
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @86
    @65
    @162
    @87
    adantr
    #
    @86
    @10
    @162
    @155
    adantr
    #
    @86
    @21
    @162
    @88
    adantr
    #
    @86
    @29
    @162
    @94
    adantr
    #
    @164
    @24
    @15
    @0
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @165
    @168
    @167
    @166
    @164
    cC
    @15
    @0
    @24
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @165
    @86
    @73
    @162
    @126
    adantr
    #
    @167
    @166
    @168
    @164
    cC
    @15
    @0
    cs3
    cC
    @6
    @0
    cs3
    @134
    @164
    cC
    @15
    @0
    @0
    cC
    @6
    @164
    cC
    eqidd
    @86
    @162
    simpr
    #
    @164
    @0
    eqidd
    s3eqd
    @164
    @0
    @6
    cC
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @165
    @166
    @86
    @83
    @162
    @91
    adantr
    #
    @169
    @164
    @32
    @6
    cC
    @0
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @165
    @86
    @38
    @162
    @90
    adantr
    #
    @171
    @169
    @166
    @86
    @32
    @6
    cC
    cs3
    @134
    wcel
    #
    @162
    @86
    @173
    @32
    cC
    c.mi
    co
    #
    @32
    @62
    c.mi
    co
    #
    wceq
    @86
    @174
    @32
    @52
    c.mi
    co
    @175
    @86
    cC
    @32
    @52
    @32
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @126
    @90
    @127
    @90
    @86
    @51
    @15
    @52
    cP
    @32
    cG
    cI
    c.mi
    @32
    @41
    @15
    cC
    isperp.p
    isperp.d
    isperp.i
    @87
    @123
    @88
    @126
    @125
    @88
    @127
    @90
    @90
    @60
    @41
    @15
    wne
    @84
    @146
    adantr
    @131
    @132
    @86
    @15
    @41
    @15
    @51
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @88
    @123
    @88
    @125
    @149
    tgcgrcomlr
    @150
    @86
    @32
    @41
    @32
    @51
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @90
    @123
    @90
    @125
    @86
    @32
    @51
    c.mi
    co
    @32
    @41
    c.mi
    co
    @86
    @32
    @41
    cP
    @25
    cG
    cI
    cL
    @50
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @90
    @121
    @123
    mircgr
    eqcomd
    tgcgrcomlr
    @86
    @34
    eqidd
    axtg5seg
    tgcgrcomlr
    @86
    @52
    @62
    @32
    c.mi
    @151
    oveq2d
    eqtrd
    @86
    @32
    @6
    cC
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @90
    @91
    @126
    israg
    mpbird
    adantr
    @164
    @32
    @15
    @6
    @86
    @32
    @15
    wne
    @162
    @120
    adantr
    @170
    neeqtrd
    @164
    @32
    @6
    @0
    cL
    co
    #
    wcel
    @6
    @0
    wceq
    @164
    @32
    @15
    @0
    cL
    co
    @176
    @164
    cP
    cG
    cI
    cL
    @15
    @0
    @32
    isperp.p
    isperp.i
    isperp.l
    @165
    @167
    @166
    @172
    @164
    @0
    @15
    @164
    @0
    cC
    @0
    @15
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @165
    @166
    @169
    @166
    @167
    @86
    @18
    @17
    wceq
    @162
    @156
    adantr
    @86
    @143
    @162
    @157
    adantr
    tgcgrneq
    necomd
    @86
    @32
    @154
    wcel
    @162
    @159
    adantr
    lncom
    @164
    @15
    @6
    @0
    cL
    @170
    oveq1d
    eleqtrd
    orcd
    ragcol
    ragcom
    eqeltrd
    @86
    cC
    @15
    wne
    @162
    @115
    adantr
    @86
    cC
    @15
    @24
    cL
    co
    wcel
    @163
    wo
    @162
    @86
    cP
    cG
    cI
    cL
    @15
    @24
    cC
    isperp.p
    isperp.l
    isperp.i
    @87
    @88
    @94
    @126
    @86
    cC
    @24
    @15
    cP
    cG
    cI
    c.mi
    isperp.p
    isperp.d
    isperp.i
    @87
    @126
    @94
    @88
    @128
    tgbtwncom
    btwncolg3
    adantr
    ragcol
    ragcom
    @60
    @137
    @84
    @162
    @140
    ad2antrr
    ragflat
    @164
    @15
    @24
    @86
    @15
    @24
    wne
    @162
    @118
    adantr
    neneqd
    pm2.65da
    neqned
    @86
    @15
    @6
    cC
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @88
    @91
    @126
    @86
    @15
    @6
    cC
    cs3
    @134
    wcel
    @55
    @15
    @62
    c.mi
    co
    #
    wceq
    @86
    @55
    @54
    @177
    @150
    @86
    @52
    @62
    @15
    c.mi
    @151
    oveq2d
    eqtrd
    @86
    @15
    @6
    cC
    cP
    @25
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @87
    @88
    @91
    @126
    israg
    mpbird
    ragcom
    ragperp
    jca
    ex
    reximdv2
    mpd
    @49
    vd
    @15
    cC
    cP
    cG
    cI
    c.mi
    @51
    @15
    isperp.p
    isperp.d
    isperp.i
    @70
    @124
    @80
    @80
    @76
    axtgsegcon
    r19.29a
    @40
    vq
    @15
    @0
    cP
    cG
    cI
    c.mi
    @24
    @15
    isperp.p
    isperp.d
    isperp.i
    @69
    @92
    @79
    @79
    @104
    axtgsegcon
    r19.29a
    @31
    vz
    @15
    @24
    cP
    cG
    cI
    c.mi
    @0
    @15
    isperp.p
    isperp.d
    isperp.i
    @68
    @103
    @78
    @78
    @23
    @29
    @28
    simplr
    axtgsegcon
    r19.29a
    @23
    vp
    @15
    cC
    @0
    cP
    @25
    cG
    cI
    cL
    @26
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @64
    @67
    @116
    @14
    @21
    @20
    simplr
    @75
    @102
    @22
    @16
    @19
    simprr
    midexlem
    r19.29a
    @14
    vy
    @0
    cC
    cP
    cG
    cI
    c.mi
    @1
    @0
    isperp.p
    isperp.d
    isperp.i
    @66
    @106
    @101
    @101
    @74
    axtgsegcon
    r19.29a
    wph
    va
    vb
    cA
    cP
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    tgisline
    r19.29vva
end
