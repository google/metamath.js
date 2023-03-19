include "wcel.mm"
include "cv.mm"
include "cmid.mm"
include "cfv.mm"
include "co.mm"
include "cperpg.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wreu.mm"
include "wb.mm"
include "wral.mm"
include "adantr.mm"
include "wn.mm"
include "wne.mm"
include "simpr.mm"
include "cmir.mm"
include "eqidd.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "eqid.mm"
include "midcl.mm"
include "ismidb.mm"
include "mpbird.mm"
include "crn.mm"
include "neqned.mm"
include "tgelrnln.mm"
include "simp-4r.mm"
include "tglinerflx1.mm"
include "elind.mm"
include "midbtwn.mm"
include "btwnlng1.mm"
include "tglineineq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "mircinv.mm"
include "3eqtr2rd.mm"
include "mtand.mm"
include "ad5antr.mm"
include "nne.mm"
include "sylib.mm"
include "eqeltrrd.mm"
include "perpneq.mm"
include "ex.mm"
include "con4d.mm"
include "idd.mm"
include "jaod.mm"
include "impr.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "midid.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "olcd.mm"
include "jca.mm"
include "impbida.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "tglnpt.mm"
include "mircl.mm"
include "oveq2.mm"
include "breq1d.mm"
include "simprl.mm"
include "wrmo.mm"
include "foot.mm"
include "reurmo.mm"
include "syl.mm"
include "nelne2.mm"
include "tgbtwnne.mm"
include "tglineelsb2.mm"
include "neneqd.mm"
include "simprr.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "perpcom.mm"
include "eqbrtrrd.mm"
include "rmoi2.mm"
include "mpbid.mm"
include "perpln1.mm"
include "tglnne.mm"
include "necomd.mm"
include "mirbtwn.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "lnrot1.mm"
include "breqtrd.mm"
include "necon1bd.mm"
include "orrd.mm"
include "footex.mm"
include "r19.29a.mm"
include "pm2.61dan.mm"

theorem lmieu
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vb: setvar b
  let vx: setvar x
  let vm: setvar m
  let va: setvar a
  let vg: setvar g
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmieu.l: |- L = ( LineG ` G )
  assume lmieu.1: |- ( ph -> D e. ran L )
  assume lmieu.a: |- ( ph -> A e. P )

  disjoint A b
  disjoint D b
  disjoint G b
  disjoint L b
  disjoint P b
  disjoint b ph
  disjoint G b
  disjoint P b
  disjoint b ph
  disjoint .- x
  disjoint A x
  disjoint b x
  disjoint D x
  disjoint G x
  disjoint I x
  disjoint L x
  disjoint P x
  disjoint ph x
  disjoint .- m
  disjoint G a
  disjoint G g
  disjoint G m
  disjoint a b
  disjoint a g
  disjoint a m
  disjoint b g
  disjoint b m
  disjoint g m
  disjoint I m
  disjoint L m
  disjoint P a
  disjoint P g
  disjoint P m
  disjoint a ph
  disjoint g ph
  disjoint m ph
  assert |- ( ph -> E! b e. P ( ( A ( midG ` G ) b ) e. D /\ ( D ( perpG ` G ) ( A L b ) \/ A = b ) ) )

  proof
    wph
    cA
    cD
    wcel
    #
    cA
    vb
    cv
    #
    cG
    cmid
    cfv
    #
    co
    #
    cD
    wcel
    #
    cD
    cA
    @1
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    cA
    @1
    wceq
    #
    wo
    #
    wa
    #
    vb
    cP
    wreu
    #
    wph
    @0
    wa
    #
    cA
    cP
    wcel
    #
    @10
    @1
    cA
    wceq
    #
    wb
    #
    vb
    cP
    wral
    @11
    wph
    @13
    @0
    lmieu.a
    adantr
    #
    @12
    @15
    vb
    cP
    @12
    @1
    cP
    wcel
    #
    wa
    #
    @10
    @14
    @18
    @10
    wa
    cA
    @1
    @18
    @4
    @9
    @8
    @18
    @4
    wa
    #
    @7
    @8
    @8
    @19
    @8
    @7
    @19
    @8
    wn
    #
    @7
    wn
    @19
    @20
    wa
    #
    @7
    cD
    @5
    wne
    #
    @21
    @22
    @8
    @19
    @20
    simpr
    #
    @21
    @22
    wa
    #
    @1
    cA
    @3
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    cA
    cA
    @25
    cfv
    #
    cfv
    cA
    @21
    @1
    @27
    wceq
    #
    @22
    @21
    @29
    @3
    @3
    wceq
    @21
    @3
    eqidd
    @21
    cA
    @1
    cP
    @25
    cG
    cI
    @3
    c.mi
    ismid.p
    ismid.d
    ismid.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    @17
    @4
    @20
    ismid.g
    ad4antr
    #
    wph
    cG
    c2
    cstrkgld
    wbr
    #
    @0
    @17
    @4
    @20
    ismid.1
    ad4antr
    #
    @12
    @13
    @17
    @4
    @20
    @16
    ad3antrrr
    #
    @12
    @17
    @4
    @20
    simpllr
    #
    @25
    eqid
    #
    @21
    cA
    @1
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @31
    @33
    @34
    @35
    midcl
    #
    ismidb
    mpbird
    adantr
    @24
    cA
    @28
    @26
    @24
    cA
    @3
    @25
    @24
    cD
    @5
    cP
    cG
    cI
    cL
    cA
    @3
    ismid.p
    ismid.i
    lmieu.l
    @21
    @30
    @22
    @31
    adantr
    #
    @21
    cD
    cL
    crn
    #
    wcel
    #
    @22
    wph
    @40
    @0
    @17
    @4
    @20
    lmieu.1
    ad4antr
    adantr
    @24
    cP
    cG
    cI
    cL
    cA
    @1
    ismid.p
    ismid.i
    lmieu.l
    @38
    @21
    @13
    @22
    @34
    adantr
    #
    @21
    @17
    @22
    @35
    adantr
    #
    @21
    cA
    @1
    wne
    #
    @22
    @21
    cA
    @1
    @23
    neqned
    #
    adantr
    #
    tgelrnln
    @21
    @22
    simpr
    @24
    cD
    @5
    cA
    @21
    @0
    @22
    wph
    @0
    @17
    @4
    @20
    simp-4r
    adantr
    @24
    cP
    cA
    @1
    cG
    cI
    cL
    ismid.p
    ismid.i
    lmieu.l
    @38
    @41
    @42
    @45
    tglinerflx1
    elind
    @24
    cD
    @5
    @3
    @18
    @4
    @20
    @22
    simpllr
    @21
    @3
    @5
    wcel
    @22
    @21
    cP
    cG
    cI
    cL
    cA
    @1
    @3
    ismid.p
    ismid.i
    lmieu.l
    @31
    @34
    @35
    @37
    @44
    @21
    cA
    @1
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @31
    @33
    @34
    @35
    midbtwn
    btwnlng1
    adantr
    elind
    tglineineq
    fveq2d
    fveq1d
    @24
    cA
    cP
    @25
    cG
    cI
    cL
    @28
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @36
    @38
    @41
    @28
    eqid
    mircinv
    3eqtr2rd
    mtand
    #
    @21
    @7
    wa
    #
    cD
    @5
    cP
    cG
    cI
    cL
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    wph
    @30
    @0
    @17
    @4
    @20
    @7
    ismid.g
    ad5antr
    wph
    @40
    @0
    @17
    @4
    @20
    @7
    lmieu.1
    ad5antr
    #
    @47
    cD
    @5
    @39
    @21
    cD
    @5
    wceq
    #
    @7
    @21
    @22
    wn
    @49
    @46
    cD
    @5
    nne
    sylib
    adantr
    @48
    eqeltrrd
    @21
    @7
    simpr
    perpneq
    mtand
    ex
    con4d
    @19
    @8
    idd
    jaod
    impr
    eqcomd
    @18
    @14
    wa
    #
    @4
    @9
    @50
    @3
    cA
    cD
    @50
    @3
    cA
    cA
    @2
    co
    #
    cA
    @50
    @1
    cA
    cA
    @2
    @18
    @14
    simpr
    #
    oveq2d
    wph
    @51
    cA
    wceq
    @0
    @17
    @14
    wph
    cA
    cA
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmieu.a
    lmieu.a
    midid
    ad3antrrr
    eqtrd
    wph
    @0
    @17
    @14
    simpllr
    eqeltrd
    @50
    @8
    @7
    @50
    @1
    cA
    @52
    eqcomd
    olcd
    jca
    impbida
    ralrimiva
    @10
    vb
    cP
    cA
    reu6i
    syl2anc
    wph
    @0
    wn
    #
    wa
    #
    cA
    vx
    cv
    #
    cL
    co
    #
    cD
    @6
    wbr
    #
    @11
    vx
    cD
    @54
    @55
    cD
    wcel
    #
    wa
    #
    @57
    wa
    #
    cA
    @55
    @25
    cfv
    #
    cfv
    #
    cP
    wcel
    @10
    @1
    @62
    wceq
    #
    wb
    #
    vb
    cP
    wral
    @11
    @60
    @55
    cP
    @25
    cG
    cI
    cL
    @61
    c.mi
    cA
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @36
    @54
    @30
    @58
    @57
    wph
    @30
    @53
    ismid.g
    adantr
    #
    ad2antrr
    #
    @60
    cD
    cP
    cG
    cI
    cL
    @55
    ismid.p
    lmieu.l
    ismid.i
    @66
    @54
    @40
    @58
    @57
    wph
    @40
    @53
    lmieu.1
    adantr
    #
    ad2antrr
    #
    @54
    @58
    @57
    simplr
    #
    tglnpt
    #
    @61
    eqid
    #
    @54
    @13
    @58
    @57
    wph
    @13
    @53
    lmieu.a
    adantr
    #
    ad2antrr
    #
    mircl
    @60
    @64
    vb
    cP
    @60
    @17
    wa
    #
    @10
    @63
    @74
    @10
    wa
    #
    @63
    @3
    @55
    wceq
    #
    @75
    @55
    @3
    @75
    @57
    cA
    @3
    cL
    co
    #
    cD
    @6
    wbr
    vx
    cD
    @3
    @55
    @3
    wceq
    @56
    @77
    cD
    @6
    @55
    @3
    cA
    cL
    oveq2
    breq1d
    @74
    @4
    @9
    simprl
    #
    @54
    @57
    vx
    cD
    wrmo
    #
    @58
    @57
    @17
    @10
    @54
    @57
    vx
    cD
    wreu
    @79
    @54
    vx
    cD
    cA
    cP
    cG
    cI
    cL
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @65
    @67
    @72
    wph
    @53
    simpr
    #
    foot
    @57
    vx
    cD
    reurmo
    syl
    ad4antr
    @60
    @58
    @17
    @10
    @69
    ad2antrr
    @59
    @57
    @17
    @10
    simpllr
    @75
    @5
    @77
    cD
    @6
    @75
    cP
    cA
    @1
    @3
    cG
    cI
    cL
    ismid.p
    ismid.i
    lmieu.l
    @60
    @30
    @17
    @10
    @66
    ad2antrr
    #
    @60
    @13
    @17
    @10
    @73
    ad2antrr
    #
    @60
    @17
    @10
    simplr
    #
    @75
    cA
    @3
    @1
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @81
    @82
    @75
    cA
    @1
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @81
    wph
    @32
    @53
    @58
    @57
    @17
    @10
    ismid.1
    ad5antr
    #
    @82
    @83
    midcl
    #
    @83
    @75
    cA
    @1
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @81
    @84
    @82
    @83
    midbtwn
    #
    @75
    @4
    @53
    @3
    cA
    wne
    @78
    @54
    @53
    @58
    @57
    @17
    @10
    @80
    ad4antr
    @3
    cA
    cD
    nelne2
    syl2anc
    #
    tgbtwnne
    #
    @85
    @87
    @75
    cP
    cG
    cI
    cL
    cA
    @1
    @3
    ismid.p
    ismid.i
    lmieu.l
    @81
    @82
    @83
    @85
    @88
    @86
    btwnlng1
    tglineelsb2
    @75
    cD
    @5
    cP
    cG
    cI
    cL
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @81
    @60
    @40
    @17
    @10
    @68
    ad2antrr
    @75
    cP
    cG
    cI
    cL
    cA
    @1
    ismid.p
    ismid.i
    lmieu.l
    @81
    @82
    @83
    @88
    tgelrnln
    @75
    @20
    @7
    @75
    cA
    @1
    @88
    neneqd
    @75
    @8
    @7
    @75
    @7
    @8
    @74
    @4
    @9
    simprr
    orcomd
    ord
    mpd
    perpcom
    eqbrtrrd
    rmoi2
    eqcomd
    @75
    cA
    @1
    cP
    @25
    cG
    cI
    @55
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @81
    @84
    @82
    @83
    @36
    @60
    @55
    cP
    wcel
    #
    @17
    @10
    @70
    ad2antrr
    ismidb
    mpbird
    @74
    @63
    wa
    #
    @4
    @9
    @90
    @3
    @55
    cD
    @90
    @63
    @76
    @74
    @63
    simpr
    @90
    cA
    @1
    cP
    @25
    cG
    cI
    @55
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @60
    @30
    @17
    @63
    @66
    ad2antrr
    #
    wph
    @32
    @53
    @58
    @57
    @17
    @63
    ismid.1
    ad5antr
    @60
    @13
    @17
    @63
    @73
    ad2antrr
    #
    @60
    @17
    @63
    simplr
    @36
    @60
    @89
    @17
    @63
    @70
    ad2antrr
    #
    ismidb
    mpbid
    @60
    @58
    @17
    @63
    @69
    ad2antrr
    eqeltrd
    @90
    @7
    @8
    @90
    @7
    cA
    @1
    @90
    @43
    @7
    @90
    @43
    wa
    #
    cD
    @56
    @5
    @6
    @94
    @56
    cD
    cP
    cG
    cI
    cL
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @90
    @30
    @43
    @91
    adantr
    #
    @94
    @56
    cD
    cG
    cL
    lmieu.l
    @95
    @59
    @57
    @17
    @63
    @43
    simp-4r
    #
    perpln1
    #
    @60
    @40
    @17
    @63
    @43
    @68
    ad3antrrr
    @96
    perpcom
    @94
    cP
    cA
    @55
    @1
    cG
    cI
    cL
    ismid.p
    ismid.i
    lmieu.l
    @95
    @90
    @13
    @43
    @92
    adantr
    #
    @90
    @89
    @43
    @93
    adantr
    #
    @94
    cP
    cG
    cI
    cL
    cA
    @55
    ismid.p
    ismid.i
    lmieu.l
    @95
    @98
    @99
    @97
    tglnne
    #
    @60
    @17
    @63
    @43
    simpllr
    #
    @94
    cA
    @1
    @90
    @43
    simpr
    necomd
    #
    @94
    cP
    cG
    cI
    cL
    cA
    @55
    @1
    ismid.p
    ismid.i
    lmieu.l
    @95
    @98
    @99
    @101
    @100
    @94
    cP
    cG
    cI
    cL
    @1
    cA
    @55
    ismid.p
    ismid.i
    lmieu.l
    @95
    @101
    @98
    @99
    @102
    @94
    @55
    @62
    cA
    cI
    co
    @1
    cA
    cI
    co
    @94
    @55
    cA
    cP
    @25
    cG
    cI
    cL
    @61
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @36
    @95
    @99
    @71
    @98
    mirbtwn
    @94
    @1
    @62
    cA
    cI
    @74
    @63
    @43
    simplr
    oveq1d
    eleqtrrd
    btwnlng1
    @102
    lnrot1
    tglineelsb2
    breqtrd
    ex
    necon1bd
    orrd
    jca
    impbida
    ralrimiva
    @10
    vb
    cP
    @62
    reu6i
    syl2anc
    @54
    vx
    cD
    cA
    cP
    cG
    cI
    cL
    c.mi
    ismid.p
    ismid.d
    ismid.i
    lmieu.l
    @65
    @67
    @72
    @80
    footex
    r19.29a
    pm2.61dan
end
