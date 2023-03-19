include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cstrkg.mm"
include "adantr.mm"
include "eqid.mm"
include "simprl.mm"
include "wn.mm"
include "wo.mm"
include "necomd.mm"
include "neneqd.mm"
include "perpln2.mm"
include "tglnne.mm"
include "jca.mm"
include "cs3.mm"
include "crag.mm"
include "tglinerflx2.mm"
include "cperpg.mm"
include "tglinecom.mm"
include "eqbrtrrd.mm"
include "perprag.mm"
include "simpr.mm"
include "orcd.mm"
include "ragflat3.mm"
include "oran.mm"
include "sylib.mm"
include "pm2.65da.mm"
include "neleqtrrd.mm"
include "wne.mm"
include "pm4.56.mm"
include "ncolrot2.mm"
include "simprrr.mm"
include "tgbtwncom.mm"
include "simprrl.mm"
include "coltr3.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "tgbtwnne.mm"
include "israg.mm"
include "mpbid.mm"
include "ad3antrrr.mm"
include "mircl.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "mirbtwn.mm"
include "ad4antr.mm"
include "ad5antr.mm"
include "wbr.mm"
include "simp-5r.mm"
include "simprd.mm"
include "simpld.mm"
include "simpllr.mm"
include "simprr.mm"
include "mideulem2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqtrd.mm"
include "midexlem.mm"
include "r19.29a.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "mircgr.mm"
include "tgcgrcomlr.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "tgcgrextend.mm"
include "axtgcgrrflx.mm"
include "colcom.mm"
include "colrot1.mm"
include "ragcol.mm"
include "tgifscgr.mm"
include "eqtr4d.mm"
include "axtgsegcon.mm"
include "btwncolg1.mm"
include "symquadlem.mm"
include "ismir.mm"
include "axtgpasch.mm"
include "reximddv.mm"

theorem opphllem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume mideu.s: |- S = ( pInvG ` G )
  assume mideu.1: |- ( ph -> A e. P )
  assume mideu.2: |- ( ph -> B e. P )
  assume mideulem.1: |- ( ph -> A =/= B )
  assume mideulem.2: |- ( ph -> Q e. P )
  assume mideulem.3: |- ( ph -> O e. P )
  assume mideulem.4: |- ( ph -> T e. P )
  assume mideulem.5: |- ( ph -> ( A L B ) ( perpG ` G ) ( Q L B ) )
  assume mideulem.6: |- ( ph -> ( A L B ) ( perpG ` G ) ( A L O ) )
  assume mideulem.7: |- ( ph -> T e. ( A L B ) )
  assume mideulem.8: |- ( ph -> T e. ( Q I O ) )
  assume opphllem.1: |- ( ph -> R e. P )
  assume opphllem.2: |- ( ph -> R e. ( B I Q ) )
  assume opphllem.3: |- ( ph -> ( A .- O ) = ( B .- R ) )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint I x
  disjoint O x
  disjoint P x
  disjoint Q x
  disjoint R x
  disjoint T x
  disjoint ph x
  disjoint .- m
  disjoint .- r
  disjoint .- s
  disjoint .- y
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint A m
  disjoint A r
  disjoint A s
  disjoint A y
  disjoint B m
  disjoint B r
  disjoint B s
  disjoint B y
  disjoint G r
  disjoint G y
  disjoint I m
  disjoint I r
  disjoint I s
  disjoint I y
  disjoint L m
  disjoint L s
  disjoint L y
  disjoint O m
  disjoint O r
  disjoint O s
  disjoint O y
  disjoint P m
  disjoint P r
  disjoint P s
  disjoint P y
  disjoint Q m
  disjoint Q r
  disjoint Q s
  disjoint Q y
  disjoint R m
  disjoint R s
  disjoint R y
  disjoint S m
  disjoint S r
  disjoint S s
  disjoint S y
  disjoint T m
  disjoint T s
  disjoint T y
  disjoint m ph
  disjoint ph r
  disjoint ph s
  disjoint ph y
  assert |- ( ph -> E. x e. P ( B = ( ( S ` x ) ` A ) /\ O = ( ( S ` x ) ` R ) ) )

  proof
    wph
    vx
    cv
    #
    cT
    cB
    cI
    co
    wcel
    #
    @0
    cR
    cO
    cI
    co
    wcel
    #
    wa
    #
    cB
    cA
    @0
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    cO
    cR
    @4
    cfv
    wceq
    #
    wa
    vx
    cP
    wph
    @0
    cP
    wcel
    #
    @3
    wa
    #
    wa
    #
    @6
    @7
    @10
    cB
    cO
    cA
    cR
    cP
    cS
    cG
    cI
    cL
    @4
    c.mi
    @0
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
    @9
    colperpex.g
    adantr
    #
    @4
    eqid
    #
    wph
    cB
    cP
    wcel
    #
    @9
    mideu.2
    adantr
    #
    wph
    cO
    cP
    wcel
    #
    @9
    mideulem.3
    adantr
    #
    wph
    cA
    cP
    wcel
    #
    @9
    mideu.1
    adantr
    #
    wph
    cR
    cP
    wcel
    #
    @9
    opphllem.1
    adantr
    #
    wph
    @8
    @3
    simprl
    #
    @10
    cP
    cG
    cI
    cL
    cA
    cB
    cO
    colperpex.p
    colperpex.l
    colperpex.i
    @12
    @19
    @15
    @17
    @10
    cO
    cA
    cB
    cL
    co
    #
    wcel
    #
    wn
    #
    cA
    cB
    wceq
    #
    wn
    #
    wa
    @24
    @26
    wo
    wn
    @10
    @25
    @27
    @10
    @23
    cB
    cA
    cL
    co
    #
    cO
    wph
    cO
    @28
    wcel
    #
    wn
    @9
    wph
    @29
    cB
    cA
    wceq
    #
    wn
    #
    cO
    cA
    wceq
    #
    wn
    #
    wa
    #
    wph
    @29
    wa
    #
    @31
    @33
    wph
    @31
    @29
    wph
    cB
    cA
    wph
    cA
    cB
    mideulem.1
    necomd
    #
    neneqd
    adantr
    wph
    @33
    @29
    wph
    cO
    cA
    wph
    cA
    cO
    wph
    cP
    cG
    cI
    cL
    cA
    cO
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    mideu.1
    mideulem.3
    wph
    @23
    cA
    cO
    cL
    co
    #
    cG
    cL
    colperpex.l
    colperpex.g
    mideulem.6
    perpln2
    tglnne
    necomd
    neneqd
    adantr
    jca
    @35
    @30
    @32
    wo
    @34
    wn
    @35
    cB
    cA
    cO
    cP
    cS
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    wph
    @11
    @29
    colperpex.g
    adantr
    wph
    @14
    @29
    mideu.2
    adantr
    wph
    @18
    @29
    mideu.1
    adantr
    wph
    @16
    @29
    mideulem.3
    adantr
    wph
    cB
    cA
    cO
    cs3
    cG
    crag
    cfv
    #
    wcel
    #
    @29
    wph
    cB
    cA
    cA
    cO
    cP
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    colperpex.g
    mideu.2
    mideu.1
    wph
    cP
    cB
    cA
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    mideu.2
    mideu.1
    @36
    tglinerflx2
    mideulem.3
    wph
    @23
    @28
    @37
    cG
    cperpg
    cfv
    #
    wph
    cP
    cA
    cB
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    colperpex.g
    mideu.1
    mideu.2
    mideulem.1
    tglinecom
    #
    mideulem.6
    eqbrtrrd
    perprag
    #
    adantr
    @35
    @29
    @30
    wph
    @29
    simpr
    orcd
    ragflat3
    @30
    @32
    oran
    sylib
    pm2.65da
    #
    adantr
    wph
    @23
    @28
    wceq
    @9
    @41
    adantr
    neleqtrrd
    @10
    cA
    cB
    wph
    cA
    cB
    wne
    #
    @9
    mideulem.1
    adantr
    #
    neneqd
    jca
    @24
    @26
    pm4.56
    sylib
    ncolrot2
    @10
    cO
    @0
    cR
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @17
    @22
    @21
    @10
    cR
    @0
    cO
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @21
    @22
    @17
    wph
    @8
    @1
    @2
    simprrr
    #
    tgbtwncom
    #
    @10
    @0
    @23
    wcel
    #
    @25
    @0
    cO
    wne
    @10
    cT
    cA
    cB
    @0
    cP
    cG
    cI
    cL
    colperpex.p
    colperpex.i
    colperpex.l
    @12
    wph
    cT
    cP
    wcel
    #
    @9
    mideulem.4
    adantr
    #
    @19
    @15
    @22
    wph
    cT
    @23
    wcel
    #
    @9
    mideulem.7
    adantr
    #
    wph
    @8
    @1
    @2
    simprrl
    coltr3
    #
    wph
    @25
    @9
    wph
    @23
    @28
    cO
    @43
    @41
    neleqtrrd
    adantr
    @0
    cO
    @23
    nelne2
    syl2anc
    tgbtwnne
    @10
    @0
    cO
    cA
    cS
    cfv
    #
    cfv
    #
    vs
    cv
    #
    cI
    co
    wcel
    #
    @0
    @56
    c.mi
    co
    @0
    cR
    c.mi
    co
    wceq
    #
    wa
    #
    cB
    cO
    c.mi
    co
    #
    cA
    cR
    c.mi
    co
    #
    wceq
    vs
    cP
    @10
    @56
    cP
    wcel
    #
    wa
    #
    @59
    wa
    #
    @60
    cB
    @55
    c.mi
    co
    #
    @61
    wph
    @60
    @65
    wceq
    #
    @9
    @62
    @59
    wph
    @39
    @66
    @42
    wph
    cB
    cA
    cO
    cP
    cS
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    colperpex.g
    mideu.2
    mideu.1
    mideulem.3
    israg
    mpbid
    ad3antrrr
    @64
    @55
    cA
    cO
    cR
    cP
    cR
    cB
    cG
    @55
    cI
    @56
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    wph
    @11
    @9
    @62
    @59
    colperpex.g
    ad3antrrr
    #
    @10
    @55
    cP
    wcel
    @62
    @59
    @10
    cA
    cP
    cS
    cG
    cI
    cL
    @54
    c.mi
    cO
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @12
    @19
    @54
    eqid
    #
    @17
    mircl
    #
    ad2antrr
    #
    wph
    @18
    @9
    @62
    @59
    mideu.1
    ad3antrrr
    #
    wph
    @16
    @9
    @62
    @59
    mideulem.3
    ad3antrrr
    #
    wph
    @20
    @9
    @62
    @59
    opphllem.1
    ad3antrrr
    #
    @73
    wph
    @14
    @9
    @62
    @59
    mideu.2
    ad3antrrr
    #
    @10
    @62
    @59
    simplr
    #
    @70
    @64
    cA
    cO
    cP
    cS
    cG
    cI
    cL
    @54
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @71
    @68
    @72
    mirbtwn
    #
    @64
    cB
    @56
    cB
    cS
    cfv
    #
    cfv
    #
    @56
    cI
    co
    cR
    @56
    cI
    co
    @64
    cB
    @56
    cP
    cS
    cG
    cI
    cL
    @77
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @74
    @77
    eqid
    #
    @75
    mirbtwn
    @64
    cR
    @78
    @56
    cI
    @64
    cR
    @56
    vm
    cv
    #
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    cR
    @78
    wceq
    vm
    cP
    @64
    @80
    cP
    wcel
    #
    wa
    #
    @83
    wa
    #
    cR
    @82
    @78
    @85
    @83
    simpr
    #
    @86
    @56
    @81
    @77
    @86
    @80
    cB
    cS
    @86
    cB
    @80
    @86
    cA
    cB
    cP
    cQ
    cR
    cS
    cT
    cG
    cI
    cL
    @80
    c.mi
    cO
    @0
    @56
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    @64
    @11
    @84
    @83
    @67
    ad2antrr
    mideu.s
    @64
    @18
    @84
    @83
    @71
    ad2antrr
    @64
    @14
    @84
    @83
    @74
    ad2antrr
    @10
    @44
    @62
    @59
    @84
    @83
    @45
    ad4antr
    wph
    cQ
    cP
    wcel
    @9
    @62
    @59
    @84
    @83
    mideulem.2
    ad5antr
    @64
    @16
    @84
    @83
    @72
    ad2antrr
    @10
    @49
    @62
    @59
    @84
    @83
    @50
    ad4antr
    wph
    @23
    cQ
    cB
    cL
    co
    @40
    wbr
    @9
    @62
    @59
    @84
    @83
    mideulem.5
    ad5antr
    wph
    @23
    @37
    @40
    wbr
    @9
    @62
    @59
    @84
    @83
    mideulem.6
    ad5antr
    @10
    @51
    @62
    @59
    @84
    @83
    @52
    ad4antr
    wph
    cT
    cQ
    cO
    cI
    co
    wcel
    @9
    @62
    @59
    @84
    @83
    mideulem.8
    ad5antr
    @64
    @20
    @84
    @83
    @73
    ad2antrr
    wph
    cR
    cB
    cQ
    cI
    co
    wcel
    @9
    @62
    @59
    @84
    @83
    opphllem.2
    ad5antr
    wph
    cA
    cO
    c.mi
    co
    #
    cB
    cR
    c.mi
    co
    #
    wceq
    #
    @9
    @62
    @59
    @84
    @83
    opphllem.3
    ad5antr
    @64
    @8
    @84
    @83
    @10
    @8
    @62
    @59
    @22
    ad2antrr
    #
    ad2antrr
    @86
    @1
    @2
    @86
    @8
    @3
    wph
    @9
    @62
    @59
    @84
    @83
    simp-5r
    simprd
    #
    simpld
    @86
    @1
    @2
    @92
    simprd
    @64
    @62
    @84
    @83
    @75
    ad2antrr
    @86
    @57
    @58
    @63
    @59
    @84
    @83
    simpllr
    simpld
    @64
    @58
    @84
    @83
    @63
    @57
    @58
    simprr
    #
    ad2antrr
    @64
    @84
    @83
    simplr
    @87
    mideulem2
    eqcomd
    fveq2d
    fveq1d
    eqtrd
    @64
    vm
    @56
    cR
    @0
    cP
    cS
    cG
    cI
    cL
    @81
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @81
    eqid
    @75
    @73
    @91
    @93
    midexlem
    r19.29a
    #
    oveq1d
    eleqtrrd
    #
    @64
    @55
    cA
    cO
    cR
    cP
    cB
    @56
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @70
    @71
    @72
    @73
    @74
    @75
    @76
    @95
    @64
    cA
    @55
    cB
    cR
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @71
    @70
    @74
    @73
    @64
    cA
    @55
    c.mi
    co
    @88
    @89
    @64
    cA
    cO
    cP
    cS
    cG
    cI
    cL
    @54
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @71
    @68
    @72
    mircgr
    wph
    @90
    @9
    @62
    @59
    opphllem.3
    ad3antrrr
    #
    eqtrd
    tgcgrcomlr
    @64
    @88
    @89
    cB
    @78
    c.mi
    co
    cB
    @56
    c.mi
    co
    @96
    @64
    cR
    @78
    cB
    c.mi
    @94
    oveq2d
    @64
    cB
    @56
    cP
    cS
    cG
    cI
    cL
    @77
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @74
    @79
    @75
    mircgr
    3eqtrd
    #
    tgcgrextend
    @97
    @64
    cP
    cG
    cI
    c.mi
    @55
    cR
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @70
    @73
    axtgcgrrflx
    @64
    cO
    cR
    c.mi
    co
    cR
    cO
    c.mi
    co
    @56
    @55
    c.mi
    co
    @64
    cP
    cG
    cI
    c.mi
    cO
    cR
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @72
    @73
    axtgcgrrflx
    @64
    cR
    @0
    cO
    @56
    cP
    @0
    @55
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @73
    @91
    @72
    @75
    @91
    @70
    @10
    @2
    @62
    @59
    @46
    ad2antrr
    @64
    @55
    @0
    @56
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @70
    @91
    @75
    @63
    @57
    @58
    simprl
    tgbtwncom
    @64
    @56
    @0
    c.mi
    co
    cR
    @0
    c.mi
    co
    @64
    @0
    @56
    @0
    cR
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @67
    @91
    @75
    @91
    @73
    @93
    tgcgrcomlr
    eqcomd
    @64
    @0
    cA
    cO
    cs3
    @38
    wcel
    @0
    cO
    c.mi
    co
    @0
    @55
    c.mi
    co
    wceq
    @64
    cB
    cA
    cO
    @0
    cP
    cS
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @74
    @71
    @72
    @91
    wph
    @39
    @9
    @62
    @59
    @42
    ad3antrrr
    @10
    cB
    cA
    wne
    @62
    @59
    @10
    cA
    cB
    @45
    necomd
    ad2antrr
    @64
    cP
    cG
    cI
    cL
    cB
    cA
    @0
    colperpex.p
    colperpex.l
    colperpex.i
    @67
    @74
    @71
    @91
    @64
    cP
    cG
    cI
    cL
    cA
    cB
    @0
    colperpex.p
    colperpex.l
    colperpex.i
    @67
    @71
    @74
    @91
    @64
    @48
    @26
    @10
    @48
    @62
    @59
    @53
    ad2antrr
    orcd
    colcom
    #
    colrot1
    ragcol
    @64
    @0
    cA
    cO
    cP
    cS
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @67
    @91
    @71
    @72
    israg
    mpbid
    tgcgrextend
    eqtrd
    tgifscgr
    eqtr4d
    @10
    vs
    @0
    cR
    cP
    cG
    cI
    c.mi
    @55
    @0
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @69
    @22
    @22
    @21
    axtgsegcon
    #
    r19.29a
    #
    @10
    cA
    cO
    cB
    cR
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @19
    @17
    @15
    @21
    wph
    @90
    @9
    opphllem.3
    adantr
    #
    tgcgrcomlr
    @10
    @59
    @0
    @28
    wcel
    @30
    wo
    vs
    cP
    @98
    @99
    r19.29a
    @10
    cP
    cG
    cI
    cL
    cO
    cR
    @0
    colperpex.p
    colperpex.l
    colperpex.i
    @12
    @17
    @21
    @22
    @47
    btwncolg1
    symquadlem
    #
    @10
    @0
    cR
    cO
    cP
    cS
    cG
    cI
    cL
    @4
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @12
    @22
    @13
    @21
    @17
    @10
    cA
    @0
    cB
    cO
    cP
    cB
    @0
    cG
    cR
    cI
    cA
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @19
    @22
    @15
    @17
    @15
    @22
    @19
    @21
    @10
    cB
    @0
    cA
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @15
    @22
    @19
    @10
    @0
    @5
    cA
    cI
    co
    cB
    cA
    cI
    co
    @10
    @0
    cA
    cP
    cS
    cG
    cI
    cL
    @4
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @12
    @22
    @13
    @19
    mirbtwn
    @10
    cB
    @5
    cA
    cI
    @102
    oveq1d
    eleqtrrd
    #
    tgbtwncom
    @103
    @10
    cP
    cG
    cI
    c.mi
    cA
    cB
    colperpex.p
    colperpex.d
    colperpex.i
    @12
    @19
    @15
    axtgcgrrflx
    @10
    @0
    cB
    c.mi
    co
    @0
    @5
    c.mi
    co
    @0
    cA
    c.mi
    co
    @10
    cB
    @5
    @0
    c.mi
    @102
    oveq2d
    @10
    @0
    cA
    cP
    cS
    cG
    cI
    cL
    @4
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    @12
    @22
    @13
    @19
    mircgr
    eqtrd
    @101
    @100
    tgifscgr
    @47
    ismir
    jca
    wph
    cP
    cT
    cG
    cI
    c.mi
    cR
    cO
    cB
    cQ
    vx
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.g
    mideulem.3
    mideu.2
    mideulem.2
    mideulem.4
    opphllem.1
    wph
    cQ
    cT
    cO
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.g
    mideulem.2
    mideulem.4
    mideulem.3
    mideulem.8
    tgbtwncom
    opphllem.2
    axtgpasch
    reximddv
end
