include "cmpt.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "cixp.mm"
include "wf.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wfn.mm"
include "wral.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "ctopon.mm"
include "adantr.mm"
include "ctop.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mptelixpg.mm"
include "syl.mm"
include "mpbird.mm"
include "fmptd.mm"
include "wal.mm"
include "df-3an.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfan.mm"
include "simprll.mm"
include "simprlr.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simprrl.mm"
include "simpld.mm"
include "simprd.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "simprrr.mm"
include "cbvixpv.mm"
include "syl6eleq.mm"
include "ptcnplem.mm"
include "anassrs.mm"
include "expr.mm"
include "rexlimdvaa.mm"
include "impr.mm"
include "sylan2b.mm"
include "eleq2.mm"
include "eqeq2i.mm"
include "biimpi.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "alrimiv.mm"
include "eqeq1.mm"
include "exbidv.mm"
include "ralab.mm"
include "cpt.mm"
include "ctg.mm"
include "ffn.mm"
include "ptval.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "feqmptd.mm"
include "fveq2d.mm"
include "pttopon.mm"
include "eqeltrd.mm"
include "tgcnp.mm"
include "mpbir2and.mm"

theorem ptcnp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let va: setvar a
  let vn: setvar n
  let cG: class G
  let wps: wff ps
  let cW: class W
  assume ptcnp.2: |- K = ( Xt_ ` F )
  assume ptcnp.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume ptcnp.4: |- ( ph -> I e. V )
  assume ptcnp.5: |- ( ph -> F : I --> Top )
  assume ptcnp.6: |- ( ph -> D e. X )
  assume ptcnp.7: |- ( ( ph /\ k e. I ) -> ( x e. X |-> A ) e. ( ( J CnP ( F ` k ) ) ` D ) )

  disjoint k x
  disjoint D k
  disjoint D x
  disjoint I k
  disjoint I x
  disjoint J k
  disjoint k ph
  disjoint ph x
  disjoint F k
  disjoint F x
  disjoint V k
  disjoint V x
  disjoint X k
  disjoint X x
  disjoint f g
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint A f
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g z
  disjoint A g
  disjoint t u
  disjoint t w
  disjoint t z
  disjoint A t
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint f k
  disjoint f x
  disjoint D f
  disjoint g k
  disjoint g x
  disjoint D g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint u x
  disjoint D u
  disjoint w x
  disjoint D w
  disjoint x z
  disjoint D z
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint I a
  disjoint f n
  disjoint I f
  disjoint g n
  disjoint I g
  disjoint k n
  disjoint k t
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint I n
  disjoint t x
  disjoint I t
  disjoint I w
  disjoint I z
  disjoint G f
  disjoint G t
  disjoint G u
  disjoint G x
  disjoint G z
  disjoint J f
  disjoint J g
  disjoint J u
  disjoint J w
  disjoint J z
  disjoint K f
  disjoint K z
  disjoint f ph
  disjoint g ph
  disjoint ph w
  disjoint ph z
  disjoint a u
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint n u
  disjoint F n
  disjoint F u
  disjoint F w
  disjoint F z
  disjoint f ps
  disjoint V a
  disjoint V g
  disjoint V n
  disjoint V w
  disjoint W f
  disjoint W k
  disjoint W z
  disjoint X f
  disjoint X g
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X z
  assert |- ( ph -> ( x e. X |-> ( k e. I |-> A ) ) e. ( ( J CnP K ) ` D ) )

  proof
    wph
    vx
    cX
    vk
    cI
    cA
    cmpt
    #
    cmpt
    #
    cD
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    cX
    vk
    cI
    vk
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    @1
    wf
    cD
    @1
    cfv
    #
    vf
    cv
    #
    wcel
    #
    cD
    vz
    cv
    #
    wcel
    #
    @1
    @9
    cima
    #
    @7
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    wi
    #
    vf
    vg
    cv
    #
    cI
    wfn
    #
    vn
    cv
    #
    @16
    cfv
    #
    @18
    cF
    cfv
    #
    wcel
    #
    vn
    cI
    wral
    #
    @19
    @20
    cuni
    #
    wceq
    #
    vn
    cI
    vw
    cv
    #
    cdif
    #
    wral
    #
    vw
    cfn
    wrex
    #
    w3a
    #
    va
    cv
    #
    vn
    cI
    @19
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    va
    cab
    #
    wral
    #
    wph
    vx
    cX
    @0
    @5
    @1
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    @0
    @5
    wcel
    #
    cA
    @4
    wcel
    #
    vk
    cI
    wral
    #
    @38
    @40
    vk
    cI
    wph
    @2
    cI
    wcel
    #
    @37
    @40
    wph
    @42
    wa
    #
    @40
    vx
    cX
    @43
    cX
    @4
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @40
    vx
    cX
    wral
    @43
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @3
    @4
    ctopon
    cfv
    wcel
    #
    @44
    cD
    cJ
    @3
    ccnp
    co
    cfv
    wcel
    @45
    wph
    @46
    @42
    ptcnp.3
    adantr
    @43
    @3
    ctop
    wcel
    @47
    wph
    cI
    ctop
    @2
    cF
    ptcnp.5
    ffvelrnda
    @3
    @4
    @4
    eqid
    toptopon
    sylib
    #
    ptcnp.7
    cD
    @44
    cJ
    @3
    cX
    @4
    cnpf2
    syl3anc
    vx
    cX
    @4
    cA
    @44
    @44
    eqid
    fmpt
    sylibr
    r19.21bi
    an32s
    ralrimiva
    @38
    cI
    cV
    wcel
    #
    @39
    @41
    wb
    wph
    @49
    @37
    ptcnp.4
    adantr
    vk
    cI
    cA
    @4
    cV
    mptelixpg
    syl
    mpbird
    @1
    eqid
    fmptd
    wph
    @29
    @7
    @31
    wceq
    #
    wa
    #
    vg
    wex
    #
    @15
    wi
    #
    vf
    wal
    @36
    wph
    @53
    vf
    wph
    @51
    @15
    vg
    wph
    @29
    @50
    @15
    wph
    @29
    wa
    @15
    @50
    @6
    @31
    wcel
    #
    @10
    @11
    vk
    cI
    @2
    @16
    cfv
    #
    cixp
    #
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    wi
    #
    @29
    wph
    @17
    @22
    wa
    #
    @28
    wa
    @60
    @17
    @22
    @28
    df-3an
    wph
    @61
    @28
    @60
    wph
    @61
    wa
    #
    @27
    @60
    vw
    cfn
    @62
    @25
    cfn
    wcel
    #
    @27
    wa
    #
    @54
    @59
    wph
    @61
    @64
    @54
    wa
    #
    @59
    wph
    @61
    @65
    wa
    #
    vx
    vz
    cA
    cD
    vk
    cF
    @16
    cI
    cJ
    cK
    cV
    @25
    cX
    ptcnp.2
    ptcnp.3
    ptcnp.4
    ptcnp.5
    ptcnp.6
    ptcnp.7
    @61
    @65
    vk
    @61
    vk
    nfv
    @64
    @54
    vk
    @64
    vk
    nfv
    vk
    @6
    @31
    vk
    cD
    @1
    vk
    vx
    cX
    @0
    vk
    cX
    nfcv
    vk
    cI
    cA
    nfmpt1
    nfmpt
    vk
    cD
    nfcv
    nffv
    nfel1
    nfan
    nfan
    wph
    @17
    @22
    @65
    simprll
    wph
    @66
    wa
    #
    @22
    @42
    @55
    @3
    wcel
    #
    wph
    @17
    @22
    @65
    simprlr
    @21
    @68
    vn
    @2
    cI
    @18
    @2
    wceq
    #
    @19
    @55
    @20
    @3
    @18
    @2
    @16
    fveq2
    #
    @18
    @2
    cF
    fveq2
    #
    eleq12d
    rspccva
    sylan
    @67
    @63
    @27
    wph
    @61
    @64
    @54
    simprrl
    #
    simpld
    @67
    @27
    @2
    @26
    wcel
    @55
    @4
    wceq
    #
    @67
    @63
    @27
    @72
    simprd
    @24
    @73
    vn
    @2
    @26
    @69
    @19
    @55
    @23
    @4
    @70
    @69
    @20
    @3
    @71
    unieqd
    eqeq12d
    rspccva
    sylan
    @67
    @6
    @31
    @56
    wph
    @61
    @64
    @54
    simprrr
    vn
    vk
    cI
    @19
    @55
    @70
    cbvixpv
    #
    syl6eleq
    ptcnplem
    anassrs
    expr
    rexlimdvaa
    impr
    sylan2b
    @50
    @8
    @54
    @14
    @59
    @7
    @31
    @6
    eleq2
    @50
    @13
    @58
    vz
    cJ
    @50
    @12
    @57
    @10
    @50
    @7
    @56
    @11
    @50
    @7
    @56
    wceq
    @31
    @56
    @7
    @74
    eqeq2i
    biimpi
    sseq2d
    anbi2d
    rexbidv
    imbi12d
    syl5ibrcom
    expimpd
    exlimdv
    alrimiv
    @34
    @52
    @15
    vf
    va
    @30
    @7
    wceq
    #
    @33
    @51
    vg
    @75
    @32
    @50
    @29
    @30
    @7
    @31
    eqeq1
    anbi2d
    exbidv
    ralab
    sylibr
    wph
    vz
    vf
    @35
    cD
    @1
    cJ
    cK
    cX
    @5
    ptcnp.3
    wph
    cK
    cF
    cpt
    cfv
    #
    @35
    ctg
    cfv
    #
    ptcnp.2
    wph
    @49
    cF
    cI
    wfn
    #
    @76
    @77
    wceq
    ptcnp.4
    wph
    cI
    ctop
    cF
    wf
    @78
    ptcnp.5
    cI
    ctop
    cF
    ffn
    syl
    va
    vn
    vw
    cI
    @35
    vg
    cF
    cV
    @35
    eqid
    ptval
    syl2anc
    syl5eq
    wph
    cK
    vk
    cI
    @3
    cmpt
    #
    cpt
    cfv
    #
    @5
    ctopon
    cfv
    #
    wph
    cK
    @76
    @80
    ptcnp.2
    wph
    cF
    @79
    cpt
    wph
    vk
    cI
    ctop
    cF
    ptcnp.5
    feqmptd
    fveq2d
    syl5eq
    wph
    @49
    @47
    vk
    cI
    wral
    @80
    @81
    wcel
    ptcnp.4
    wph
    @47
    vk
    cI
    @48
    ralrimiva
    vk
    cI
    @4
    @80
    @3
    cV
    @80
    eqid
    pttopon
    syl2anc
    eqeltrd
    ptcnp.6
    tgcnp
    mpbir2and
end
