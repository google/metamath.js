include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "csn.mm"
include "cfv.mm"
include "cmpt2.mm"
include "crn.mm"
include "cun.mm"
include "wral.mm"
include "wa.mm"
include "cixp.mm"
include "simpl3.mm"
include "wceq.mm"
include "ptuni.mm"
include "3adant3.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "resixp.mm"
include "syl2anc.mm"
include "ixpeq2.mm"
include "fvres.mm"
include "unieqd.mm"
include "mprg.mm"
include "cvv.mm"
include "ssexg.mm"
include "ancoms.mm"
include "3adant2.mm"
include "fssres.mm"
include "3adant1.mm"
include "syl5eqr.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "fmptd.mm"
include "fimacnv.mm"
include "syl.mm"
include "cpt.mm"
include "pttop.mm"
include "syl5eqel.mm"
include "topopn.mm"
include "eqeltrd.mm"
include "elsni.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "ccom.mm"
include "imaco.mm"
include "cnvco.mm"
include "adantlr.mm"
include "eqidd.mm"
include "fveq1.mm"
include "fmptco.mm"
include "ad2antrl.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "sseldd.mm"
include "ptpjcn.mm"
include "syl3anc.mm"
include "simprr.mm"
include "cnima.mm"
include "imaeq2.mm"
include "rexlimdvva.mm"
include "alrimiv.mm"
include "cab.mm"
include "rnmpt2.mm"
include "raleqi.mm"
include "rexeqdv.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "sylan9bbr.mm"
include "rexbidva.mm"
include "ralab.mm"
include "bitri.mm"
include "sylibr.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "snex.mm"
include "fvex.mm"
include "abrexex.mm"
include "rgenw.mm"
include "abrexex2g.mm"
include "sylancl.mm"
include "unexg.mm"
include "sylancr.mm"
include "cfi.mm"
include "ctg.mm"
include "ptval2.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem ptrescn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  assume ptrescn.1: |- X = U. J
  assume ptrescn.2: |- J = ( Xt_ ` F )
  assume ptrescn.3: |- K = ( Xt_ ` ( F |` B ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint K x
  disjoint V x
  disjoint X x
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint A k
  disjoint u v
  disjoint u x
  disjoint A u
  disjoint v x
  disjoint A v
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint K v
  disjoint K y
  disjoint K z
  disjoint J k
  disjoint J u
  disjoint J v
  disjoint V k
  disjoint V u
  disjoint V v
  disjoint X k
  disjoint X u
  disjoint X v
  assert |- ( ( A e. V /\ F : A --> Top /\ B C_ A ) -> ( x e. X |-> ( x |` B ) ) e. ( J Cn K ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    cB
    cA
    wss
    #
    w3a
    #
    vx
    cX
    vx
    cv
    #
    cB
    cres
    #
    cmpt
    #
    cJ
    cK
    ccn
    co
    wcel
    cX
    cK
    cuni
    #
    @6
    wf
    #
    @6
    ccnv
    #
    vv
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vv
    @7
    csn
    #
    vk
    vu
    cB
    vk
    cv
    #
    cF
    cB
    cres
    #
    cfv
    #
    vz
    @7
    @14
    vz
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    #
    vu
    cv
    #
    cima
    #
    cmpt2
    #
    crn
    #
    cun
    #
    wral
    #
    @3
    vx
    cX
    @5
    @7
    @6
    @3
    @4
    cX
    wcel
    #
    wa
    #
    @5
    vk
    cB
    @14
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    @7
    @28
    @2
    @4
    vk
    cA
    @30
    cixp
    #
    wcel
    #
    @5
    @31
    wcel
    @0
    @1
    @2
    @27
    simpl3
    @3
    @33
    @27
    @3
    @32
    cX
    @4
    @3
    @32
    cJ
    cuni
    #
    cX
    @0
    @1
    @32
    @34
    wceq
    @2
    vk
    cA
    cF
    cJ
    cV
    ptrescn.2
    ptuni
    3adant3
    ptrescn.1
    syl6eqr
    eleq2d
    biimpar
    vk
    cA
    cB
    @30
    @4
    resixp
    syl2anc
    @3
    @31
    @7
    wceq
    @27
    @3
    @31
    vk
    cB
    @16
    cuni
    #
    cixp
    #
    @7
    @35
    @30
    wceq
    @36
    @31
    wceq
    vk
    cB
    vk
    cB
    @35
    @30
    ixpeq2
    @14
    cB
    wcel
    #
    @16
    @29
    @14
    cB
    cF
    fvres
    #
    unieqd
    mprg
    @3
    cB
    cvv
    wcel
    #
    cB
    ctop
    @15
    wf
    #
    @36
    @7
    wceq
    @0
    @2
    @39
    @1
    @2
    @0
    @39
    cB
    cA
    cV
    ssexg
    ancoms
    3adant2
    #
    @1
    @2
    @40
    @0
    cA
    ctop
    cB
    cF
    fssres
    3adant1
    #
    vk
    cB
    @15
    cK
    cvv
    ptrescn.3
    ptuni
    syl2anc
    syl5eqr
    adantr
    eleqtrd
    #
    @6
    eqid
    fmptd
    #
    @3
    @12
    vv
    @13
    wral
    @12
    vv
    @24
    wral
    #
    @26
    @3
    @12
    vv
    @13
    @3
    @12
    @10
    @13
    wcel
    #
    @9
    @7
    cima
    #
    cJ
    wcel
    @3
    @47
    cX
    cJ
    @3
    @8
    @47
    cX
    wceq
    @44
    cX
    @7
    @6
    fimacnv
    syl
    @3
    cJ
    ctop
    wcel
    #
    cX
    cJ
    wcel
    @0
    @1
    @48
    @2
    @0
    @1
    wa
    cJ
    cF
    cpt
    cfv
    ctop
    ptrescn.2
    cA
    cF
    cV
    pttop
    syl5eqel
    3adant3
    #
    cJ
    cX
    ptrescn.1
    topopn
    syl
    eqeltrd
    @46
    @11
    @47
    cJ
    @46
    @10
    @7
    @9
    @10
    @7
    elsni
    imaeq2d
    eleq1d
    syl5ibrcom
    ralrimiv
    @3
    @10
    @22
    wceq
    #
    vu
    @29
    wrex
    #
    vk
    cB
    wrex
    #
    @12
    wi
    #
    vv
    wal
    #
    @45
    @3
    @53
    vv
    @3
    @50
    @12
    vk
    vu
    cB
    @29
    @3
    @37
    @21
    @29
    wcel
    #
    wa
    #
    wa
    #
    @12
    @50
    @9
    @22
    cima
    #
    cJ
    wcel
    @57
    @58
    vx
    cX
    @14
    @4
    cfv
    #
    cmpt
    #
    ccnv
    #
    @21
    cima
    #
    cJ
    @57
    @58
    @9
    @20
    ccom
    #
    @21
    cima
    @62
    @9
    @20
    @21
    imaco
    @57
    @63
    @61
    @21
    @57
    @63
    @19
    @6
    ccom
    #
    ccnv
    @61
    @19
    @6
    cnvco
    @57
    @64
    @60
    @57
    @64
    vx
    cX
    @14
    @5
    cfv
    #
    cmpt
    @60
    @57
    vx
    vz
    cX
    @7
    @5
    @18
    @65
    @6
    @19
    @3
    @27
    @5
    @7
    wcel
    @56
    @43
    adantlr
    @57
    @6
    eqidd
    @57
    @19
    eqidd
    @14
    @17
    @5
    fveq1
    fmptco
    @57
    vx
    cX
    @65
    @59
    @37
    @65
    @59
    wceq
    @3
    @55
    @14
    cB
    @4
    fvres
    ad2antrl
    mpteq2dv
    eqtrd
    cnveqd
    syl5eqr
    imaeq1d
    syl5eqr
    @57
    @60
    cJ
    @29
    ccn
    co
    wcel
    #
    @55
    @62
    cJ
    wcel
    @57
    @0
    @1
    @14
    cA
    wcel
    @66
    @0
    @1
    @2
    @56
    simpl1
    @0
    @1
    @2
    @56
    simpl2
    @57
    cB
    cA
    @14
    @0
    @1
    @2
    @56
    simpl3
    @3
    @37
    @55
    simprl
    sseldd
    vx
    cA
    cF
    @14
    cJ
    cV
    cX
    ptrescn.1
    ptrescn.2
    ptpjcn
    syl3anc
    @3
    @37
    @55
    simprr
    @21
    @60
    cJ
    @29
    cnima
    syl2anc
    eqeltrd
    @50
    @11
    @58
    cJ
    @10
    @22
    @9
    imaeq2
    eleq1d
    syl5ibrcom
    rexlimdvva
    alrimiv
    @45
    @12
    vv
    vy
    cv
    #
    @22
    wceq
    #
    vu
    @16
    wrex
    #
    vk
    cB
    wrex
    #
    vy
    cab
    #
    wral
    @54
    @12
    vv
    @24
    @71
    vk
    vu
    vy
    cB
    @16
    @22
    @23
    @23
    eqid
    #
    rnmpt2
    #
    raleqi
    @70
    @52
    @12
    vv
    vy
    @67
    @10
    wceq
    #
    @69
    @51
    vk
    cB
    @37
    @69
    @68
    vu
    @29
    wrex
    @74
    @51
    @37
    @68
    vu
    @16
    @29
    @38
    rexeqdv
    @74
    @68
    @50
    vu
    @29
    @67
    @10
    @22
    eqeq1
    rexbidv
    sylan9bbr
    rexbidva
    ralab
    bitri
    sylibr
    @12
    vv
    @13
    @24
    ralunb
    sylanbrc
    @3
    vv
    @25
    @6
    cJ
    cK
    cvv
    cX
    @7
    @3
    @48
    cJ
    cX
    ctopon
    cfv
    wcel
    @49
    cJ
    cX
    ptrescn.1
    toptopon
    sylib
    @3
    @13
    cvv
    wcel
    @24
    cvv
    wcel
    @25
    cvv
    wcel
    @7
    snex
    @3
    @24
    @71
    cvv
    @73
    @3
    @39
    @69
    vy
    cab
    cvv
    wcel
    #
    vk
    cB
    wral
    @71
    cvv
    wcel
    @41
    @75
    vk
    cB
    vu
    vy
    @16
    @22
    @14
    @15
    fvex
    abrexex
    rgenw
    @69
    vk
    vy
    cB
    cvv
    cvv
    abrexex2g
    sylancl
    syl5eqel
    @13
    @24
    cvv
    cvv
    unexg
    sylancr
    @3
    @39
    @40
    cK
    @25
    cfi
    cfv
    ctg
    cfv
    wceq
    @41
    @42
    vz
    vu
    cB
    vk
    @15
    @23
    cK
    cvv
    @7
    ptrescn.3
    @7
    eqid
    #
    @72
    ptval2
    syl2anc
    @3
    cK
    ctop
    wcel
    cK
    @7
    ctopon
    cfv
    wcel
    @3
    cK
    @15
    cpt
    cfv
    #
    ctop
    ptrescn.3
    @3
    @39
    @40
    @77
    ctop
    wcel
    @41
    @42
    cB
    @15
    cvv
    pttop
    syl2anc
    syl5eqel
    cK
    @7
    @76
    toptopon
    sylib
    subbascn
    mpbir2and
end
