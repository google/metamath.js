include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "adantr.mm"
include "cstrkg.mm"
include "eqid.mm"
include "mircinv.mm"
include "simpr.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wne.mm"
include "co.mm"
include "cperpg.mm"
include "wbr.mm"
include "wo.mm"
include "cleg.mm"
include "ad2antrr.mm"
include "ad4antr.mm"
include "simplr.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "simp-5r.mm"
include "perpln1.mm"
include "tgelrnln.mm"
include "perpcom.mm"
include "tglnne.mm"
include "tglinecom.mm"
include "breqtrd.mm"
include "simpld.mm"
include "wn.mm"
include "neneqd.mm"
include "simprd.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "mideulem.mm"
include "simprl.mm"
include "simprr.mm"
include "eqcomd.mm"
include "mircom.mm"
include "necomd.mm"
include "crn.mm"
include "eqeltrd.mm"
include "3brtr3d.mm"
include "eleqtrd.mm"
include "tgbtwncom.mm"
include "reximddv.mm"
include "ad3antrrr.mm"
include "legtrid.mm"
include "mpjaodan.mm"
include "c2.mm"
include "cstrkgld.mm"
include "colperpex.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "sylibr.mm"
include "r19.29vva.mm"
include "breqtrrd.mm"
include "ex.mm"
include "reximdv.mm"
include "r19.29a.mm"
include "pm2.61dane.mm"

theorem midex
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume mideu.s: |- S = ( pInvG ` G )
  assume mideu.1: |- ( ph -> A e. P )
  assume mideu.2: |- ( ph -> B e. P )
  assume mideu.3: |- ( ph -> G TarskiGDim>= 2 )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint G x
  disjoint I x
  disjoint L x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint .- p
  disjoint .- q
  disjoint .- s
  disjoint .- t
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint A p
  disjoint A q
  disjoint A s
  disjoint A t
  disjoint A y
  disjoint p y
  disjoint q y
  disjoint s y
  disjoint t y
  disjoint x y
  disjoint B p
  disjoint B q
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint G p
  disjoint G q
  disjoint G s
  disjoint G t
  disjoint I p
  disjoint I q
  disjoint I s
  disjoint I t
  disjoint L p
  disjoint L q
  disjoint L s
  disjoint L t
  disjoint P p
  disjoint P q
  disjoint P s
  disjoint P t
  disjoint P y
  disjoint S p
  disjoint S q
  disjoint S t
  disjoint S y
  disjoint p ph
  disjoint ph q
  disjoint ph s
  disjoint ph t
  disjoint ph y
  assert |- ( ph -> E. x e. P B = ( ( S ` x ) ` A ) )

  proof
    wph
    cB
    cA
    vx
    cv
    #
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    cP
    wrex
    #
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    wa
    #
    cA
    cP
    wcel
    #
    cB
    cA
    cA
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    @4
    wph
    @7
    @5
    mideu.1
    adantr
    #
    @6
    @9
    cA
    cB
    @6
    cA
    cP
    cS
    cG
    cI
    cL
    @8
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    wph
    cG
    cstrkg
    wcel
    #
    @5
    colperpex.g
    adantr
    @11
    @8
    eqid
    mircinv
    wph
    @5
    simpr
    eqtr2d
    @3
    @10
    vx
    cA
    cP
    @0
    cA
    wceq
    #
    @2
    @9
    cB
    @13
    cA
    @1
    @8
    @0
    cA
    cS
    fveq2
    fveq1d
    eqeq2d
    rspcev
    syl2anc
    wph
    cA
    cB
    wne
    #
    wa
    #
    cB
    vq
    cv
    #
    cL
    co
    #
    cA
    cB
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    @4
    vq
    cP
    @15
    @16
    cP
    wcel
    #
    wa
    #
    @20
    wa
    #
    cA
    vp
    cv
    #
    cL
    co
    #
    @18
    @19
    wbr
    #
    vt
    cv
    #
    @18
    wcel
    #
    @5
    wo
    #
    @27
    @16
    @24
    cI
    co
    wcel
    #
    wa
    #
    wa
    #
    @4
    vp
    vt
    cP
    cP
    @23
    @24
    cP
    wcel
    #
    wa
    #
    @27
    cP
    wcel
    #
    wa
    #
    @32
    wa
    #
    cA
    @24
    c.mi
    co
    #
    cB
    @16
    c.mi
    co
    #
    cG
    cleg
    cfv
    #
    wbr
    #
    @4
    @39
    @38
    @40
    wbr
    #
    @37
    @41
    wa
    #
    vx
    cA
    cB
    cP
    @16
    cS
    @27
    cG
    cI
    cL
    c.mi
    @24
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @23
    @12
    @33
    @35
    @32
    @41
    @15
    @12
    @21
    @20
    wph
    @12
    @14
    colperpex.g
    adantr
    #
    ad2antrr
    #
    ad4antr
    #
    mideu.s
    @23
    @7
    @33
    @35
    @32
    @41
    @15
    @7
    @21
    @20
    wph
    @7
    @14
    mideu.1
    adantr
    #
    ad2antrr
    #
    ad4antr
    #
    @23
    cB
    cP
    wcel
    #
    @33
    @35
    @32
    @41
    @15
    @50
    @21
    @20
    wph
    @50
    @14
    mideu.2
    adantr
    #
    ad2antrr
    #
    ad4antr
    #
    @23
    @14
    @33
    @35
    @32
    @41
    @15
    @14
    @21
    @20
    wph
    @14
    simpr
    #
    ad2antrr
    #
    ad4antr
    #
    @23
    @21
    @33
    @35
    @32
    @41
    @15
    @21
    @20
    simplr
    #
    ad4antr
    #
    @23
    @33
    @35
    @32
    @41
    simp-4r
    @34
    @35
    @32
    @41
    simpllr
    @43
    @18
    @17
    @16
    cB
    cL
    co
    @19
    @43
    @17
    @18
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @46
    @43
    @17
    @18
    cG
    cL
    colperpex.l
    @46
    @22
    @20
    @33
    @35
    @32
    @41
    simp-5r
    #
    perpln1
    #
    @43
    cP
    cG
    cI
    cL
    cA
    cB
    colperpex.p
    colperpex.i
    colperpex.l
    @46
    @49
    @53
    @56
    tgelrnln
    #
    @59
    perpcom
    @43
    cP
    cB
    @16
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @46
    @53
    @58
    @43
    cP
    cG
    cI
    cL
    cB
    @16
    colperpex.p
    colperpex.i
    colperpex.l
    @46
    @53
    @58
    @60
    tglnne
    tglinecom
    breqtrd
    @43
    @25
    @18
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @46
    @43
    @25
    @18
    cG
    cL
    colperpex.l
    @46
    @43
    @26
    @31
    @36
    @32
    @41
    simplr
    #
    simpld
    #
    perpln1
    @61
    @63
    perpcom
    @43
    @5
    wn
    #
    @28
    @43
    cA
    cB
    @56
    neneqd
    @43
    @5
    @28
    @43
    @28
    @5
    @43
    @29
    @30
    @43
    @26
    @31
    @62
    simprd
    #
    simpld
    orcomd
    ord
    mpd
    @43
    @29
    @30
    @65
    simprd
    @37
    @41
    simpr
    mideulem
    @37
    @42
    wa
    #
    cA
    cB
    @1
    cfv
    #
    wceq
    #
    @3
    vx
    cP
    @66
    @0
    cP
    wcel
    #
    @68
    wa
    #
    wa
    #
    @2
    cB
    @71
    @0
    cB
    cA
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @66
    @12
    @70
    @23
    @12
    @33
    @35
    @32
    @42
    @45
    ad4antr
    #
    adantr
    @66
    @69
    @68
    simprl
    @1
    eqid
    @66
    @50
    @70
    @23
    @50
    @33
    @35
    @32
    @42
    @52
    ad4antr
    #
    adantr
    @71
    cA
    @67
    @66
    @69
    @68
    simprr
    eqcomd
    mircom
    eqcomd
    @66
    vx
    cB
    cA
    cP
    @24
    cS
    @27
    cG
    cI
    cL
    c.mi
    @16
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @72
    mideu.s
    @73
    @23
    @7
    @33
    @35
    @32
    @42
    @48
    ad4antr
    #
    @66
    cA
    cB
    @23
    @14
    @33
    @35
    @32
    @42
    @55
    ad4antr
    #
    necomd
    #
    @23
    @33
    @35
    @32
    @42
    simp-4r
    #
    @23
    @21
    @33
    @35
    @32
    @42
    @57
    ad4antr
    #
    @34
    @35
    @32
    @42
    simpllr
    #
    @66
    @24
    cA
    cL
    co
    #
    cB
    cA
    cL
    co
    #
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @72
    @66
    @80
    @25
    cL
    crn
    @66
    @25
    @80
    @66
    cP
    cA
    @24
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @72
    @74
    @77
    @66
    cP
    cG
    cI
    cL
    cA
    @24
    colperpex.p
    colperpex.i
    colperpex.l
    @72
    @74
    @77
    @66
    @25
    @18
    cG
    cL
    colperpex.l
    @72
    @66
    @26
    @31
    @36
    @32
    @42
    simplr
    #
    simpld
    #
    perpln1
    #
    tglnne
    tglinecom
    #
    eqcomd
    @84
    eqeltrd
    @66
    cP
    cG
    cI
    cL
    cB
    cA
    colperpex.p
    colperpex.i
    colperpex.l
    @72
    @73
    @74
    @76
    tgelrnln
    #
    @66
    @25
    @18
    @80
    @81
    @19
    @83
    @85
    @66
    cP
    cA
    cB
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @72
    @74
    @73
    @75
    tglinecom
    #
    3brtr3d
    perpcom
    @66
    @17
    @81
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @72
    @66
    @17
    @18
    cG
    cL
    colperpex.l
    @72
    @22
    @20
    @33
    @35
    @32
    @42
    simp-5r
    #
    perpln1
    @86
    @66
    @17
    @18
    @81
    @19
    @88
    @87
    breqtrd
    perpcom
    @66
    @27
    @18
    @81
    @66
    @64
    @28
    @66
    cA
    cB
    @75
    neneqd
    @66
    @5
    @28
    @66
    @28
    @5
    @66
    @29
    @30
    @66
    @26
    @31
    @82
    simprd
    #
    simpld
    orcomd
    ord
    mpd
    @87
    eleqtrd
    @66
    @16
    @27
    @24
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @72
    @78
    @79
    @77
    @66
    @29
    @30
    @89
    simprd
    tgbtwncom
    @37
    @42
    simpr
    mideulem
    reximddv
    @37
    cA
    @24
    cB
    @16
    cP
    cG
    cI
    @40
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @40
    eqid
    @23
    @12
    @33
    @35
    @32
    @45
    ad3antrrr
    @23
    @7
    @33
    @35
    @32
    @48
    ad3antrrr
    @23
    @33
    @35
    @32
    simpllr
    @23
    @50
    @33
    @35
    @32
    @52
    ad3antrrr
    @23
    @21
    @33
    @35
    @32
    @57
    ad3antrrr
    legtrid
    mpjaodan
    @23
    @26
    @31
    vt
    cP
    wrex
    wa
    #
    vp
    cP
    wrex
    @32
    vt
    cP
    wrex
    #
    vp
    cP
    wrex
    @23
    vt
    cA
    cB
    @16
    cP
    cG
    cI
    cL
    c.mi
    vp
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @45
    @48
    @52
    @57
    @55
    @15
    cG
    c2
    cstrkgld
    wbr
    #
    @21
    @20
    wph
    @92
    @14
    mideu.3
    adantr
    #
    ad2antrr
    colperpex
    @91
    @90
    vp
    cP
    @26
    @31
    vt
    cP
    r19.42v
    rexbii
    sylibr
    r19.29vva
    @15
    @17
    @81
    @19
    wbr
    #
    vs
    cv
    #
    @81
    wcel
    cB
    cA
    wceq
    wo
    @95
    cA
    @16
    cI
    co
    wcel
    wa
    vs
    cP
    wrex
    #
    wa
    #
    vq
    cP
    wrex
    @20
    vq
    cP
    wrex
    @15
    vs
    cB
    cA
    cA
    cP
    cG
    cI
    cL
    c.mi
    vq
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @44
    @51
    @47
    @47
    @15
    cA
    cB
    @54
    necomd
    @93
    colperpex
    @15
    @97
    @20
    vq
    cP
    @15
    @97
    @20
    @15
    @97
    wa
    @17
    @81
    @18
    @19
    @15
    @94
    @96
    simprl
    @15
    @18
    @81
    wceq
    @97
    @15
    cP
    cA
    cB
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @44
    @47
    @51
    @54
    tglinecom
    adantr
    breqtrrd
    ex
    reximdv
    mpd
    r19.29a
    pm2.61dane
end
