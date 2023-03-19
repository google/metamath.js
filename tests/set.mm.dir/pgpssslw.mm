include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "cpgp.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wrex.mm"
include "cslw.mm"
include "crab.mm"
include "cz.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wf.mm"
include "chash.mm"
include "cn0.mm"
include "simp2.mm"
include "elrabi.mm"
include "subgss.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2an.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "fmptd.mm"
include "frn.mm"
include "wfn.mm"
include "fvex.mm"
include "fnmpti.mm"
include "simp1.mm"
include "simp3.mm"
include "eqimss2.mm"
include "biantrud.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "breq2d.mm"
include "bitr3d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "ne0i.mm"
include "nn0red.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "adantl.mm"
include "weq.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "cdom.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "ssdomg.mm"
include "sylc.mm"
include "wb.mm"
include "syl2anc.mm"
include "hashdom.mm"
include "mpbird.mm"
include "sylan2b.mm"
include "eqbrtrd.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "ralrn.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprzcl.mm"
include "syl3anc.mm"
include "fvelrnb.mm"
include "sylib.mm"
include "rexrab.mm"
include "cprime.mm"
include "simpl3.mm"
include "pgpprm.mm"
include "simprl.mm"
include "wpss.mm"
include "wn.mm"
include "zssre.mm"
include "syl6ss.mm"
include "ad2antrr.mm"
include "simprrr.mm"
include "simprrl.mm"
include "simprd.mm"
include "sstrd.mm"
include "jca.mm"
include "eqeltrrd.mm"
include "suprub.mm"
include "syl31anc.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "simpll2.mm"
include "nn0re.mm"
include "lenlt.mm"
include "mpbid.mm"
include "csdm.mm"
include "wi.mm"
include "php3.mm"
include "ex.mm"
include "hashsdom.mm"
include "sylibrd.mm"
include "mtod.mm"
include "wo.mm"
include "sspss.mm"
include "ord.mm"
include "mpd.mm"
include "expr.mm"
include "simpld.mm"
include "eqimss.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "syl5ibcom.mm"
include "impbid.mm"
include "isslw.mm"
include "syl3anbrc.mm"
include "reximdv2.mm"

theorem pgpssslw
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let vm: setvar m
  let vw: setvar w
  let vz: setvar z
  assume pgpssslw.1: |- X = ( Base ` G )
  assume pgpssslw.2: |- S = ( G |`s H )
  assume pgpssslw.3: |- F = ( x e. { y e. ( SubGrp ` G ) | ( P pGrp ( G |`s y ) /\ H C_ y ) } |-> ( # ` x ) )

  disjoint k x
  disjoint k y
  disjoint G k
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint X k
  disjoint X x
  disjoint F k
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint k m
  disjoint k w
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint G m
  disjoint w x
  disjoint w y
  disjoint G w
  disjoint H m
  disjoint H w
  disjoint P m
  disjoint P w
  disjoint k z
  disjoint m z
  disjoint X m
  disjoint w z
  disjoint X w
  disjoint x z
  disjoint X z
  disjoint F m
  disjoint F w
  disjoint F z
  disjoint S m
  assert |- ( ( H e. ( SubGrp ` G ) /\ X e. Fin /\ P pGrp S ) -> E. k e. ( P pSyl G ) H C_ k )

  proof
    cH
    cG
    csubg
    cfv
    #
    wcel
    #
    cX
    cfn
    wcel
    #
    cP
    cS
    cpgp
    wbr
    #
    w3a
    #
    cP
    cG
    vk
    cv
    #
    cress
    co
    #
    cpgp
    wbr
    #
    cH
    @5
    wss
    #
    wa
    #
    @5
    cF
    cfv
    #
    cF
    crn
    #
    cr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vk
    @0
    wrex
    #
    @8
    vk
    cP
    cG
    cslw
    co
    #
    wrex
    @4
    @13
    vk
    cP
    cG
    vy
    cv
    #
    cress
    co
    #
    cpgp
    wbr
    #
    cH
    @17
    wss
    #
    wa
    #
    vy
    @0
    crab
    #
    wrex
    #
    @15
    @4
    @12
    @11
    wcel
    #
    @23
    @4
    @11
    cz
    wss
    #
    @11
    c0
    wne
    #
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vw
    @11
    wral
    #
    vz
    cr
    wrex
    #
    @24
    @4
    @22
    cz
    cF
    wf
    @25
    @4
    vx
    @22
    vx
    cv
    #
    chash
    cfv
    #
    cz
    cF
    @4
    @32
    @22
    wcel
    #
    wa
    #
    @33
    @35
    @32
    cfn
    wcel
    #
    @33
    cn0
    wcel
    @4
    @2
    @32
    cX
    wss
    #
    @36
    @34
    @1
    @2
    @3
    simp2
    #
    @34
    @32
    @0
    wcel
    @37
    @21
    vy
    @32
    @0
    elrabi
    cX
    @32
    cG
    pgpssslw.1
    subgss
    syl
    cX
    @32
    ssfi
    syl2an
    @32
    hashcl
    syl
    nn0zd
    pgpssslw.3
    fmptd
    @22
    cz
    cF
    frn
    syl
    #
    @4
    cH
    cF
    cfv
    #
    @11
    wcel
    #
    @26
    @4
    cF
    @22
    wfn
    #
    cH
    @22
    wcel
    #
    @41
    vx
    @22
    @33
    cF
    @32
    chash
    fvex
    pgpssslw.3
    fnmpti
    #
    @4
    @1
    @3
    @43
    @1
    @2
    @3
    simp1
    @1
    @2
    @3
    simp3
    @21
    @3
    vy
    cH
    @0
    @17
    cH
    wceq
    #
    @19
    @21
    @3
    @45
    @20
    @19
    cH
    @17
    eqimss2
    biantrud
    @45
    @18
    cS
    cP
    cpgp
    @45
    @18
    cG
    cH
    cress
    co
    cS
    @17
    cH
    cG
    cress
    oveq2
    pgpssslw.2
    syl6eqr
    breq2d
    bitr3d
    elrab
    sylanbrc
    @22
    cH
    cF
    fnfvelrn
    sylancr
    @11
    @40
    ne0i
    syl
    #
    @4
    cX
    chash
    cfv
    #
    cr
    wcel
    @27
    @47
    cle
    wbr
    #
    vw
    @11
    wral
    #
    @31
    @4
    @47
    @4
    @2
    @47
    cn0
    wcel
    @38
    cX
    hashcl
    syl
    nn0red
    @4
    vm
    cv
    #
    cF
    cfv
    #
    @47
    cle
    wbr
    #
    vm
    @22
    wral
    #
    @49
    @4
    @52
    vm
    @22
    @4
    @50
    @22
    wcel
    #
    wa
    @51
    @50
    chash
    cfv
    #
    @47
    cle
    @54
    @51
    @55
    wceq
    #
    @4
    vx
    @50
    @33
    @55
    @22
    cF
    @32
    @50
    chash
    fveq2
    pgpssslw.3
    @50
    chash
    fvex
    fvmpt
    #
    adantl
    @54
    @4
    @50
    @0
    wcel
    #
    cP
    cG
    @50
    cress
    co
    #
    cpgp
    wbr
    #
    cH
    @50
    wss
    #
    wa
    #
    wa
    #
    @55
    @47
    cle
    wbr
    #
    @21
    @62
    vy
    @50
    @0
    vy
    vm
    weq
    #
    @19
    @60
    @20
    @61
    @65
    @18
    @59
    cP
    cpgp
    @17
    @50
    cG
    cress
    oveq2
    breq2d
    @17
    @50
    cH
    sseq2
    anbi12d
    elrab
    #
    @4
    @63
    wa
    #
    @64
    @50
    cX
    cdom
    wbr
    #
    @67
    @2
    @50
    cX
    wss
    #
    @68
    @4
    @2
    @63
    @38
    adantr
    #
    @58
    @69
    @4
    @62
    cX
    @50
    cG
    pgpssslw.1
    subgss
    #
    ad2antrl
    #
    @50
    cX
    cfn
    ssdomg
    sylc
    @67
    @50
    cfn
    wcel
    #
    @2
    @64
    @68
    wb
    @67
    @2
    @69
    @73
    @70
    @72
    cX
    @50
    ssfi
    #
    syl2anc
    @70
    @50
    cX
    cfn
    hashdom
    syl2anc
    mpbird
    sylan2b
    eqbrtrd
    ralrimiva
    @42
    @49
    @53
    wb
    @44
    @48
    @52
    vw
    vm
    @22
    cF
    @27
    @51
    @47
    cle
    breq1
    ralrn
    ax-mp
    sylibr
    @30
    @49
    vz
    @47
    cr
    @28
    @47
    wceq
    @29
    @48
    vw
    @11
    @28
    @47
    @27
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vz
    vw
    @11
    suprzcl
    syl3anc
    @42
    @24
    @23
    wb
    @44
    vk
    @22
    @12
    cF
    fvelrnb
    ax-mp
    sylib
    @21
    @9
    @13
    vk
    vy
    @0
    vy
    vk
    weq
    #
    @19
    @7
    @20
    @8
    @76
    @18
    @6
    cP
    cpgp
    @17
    @5
    cG
    cress
    oveq2
    breq2d
    @17
    @5
    cH
    sseq2
    anbi12d
    #
    rexrab
    sylib
    @4
    @14
    @8
    vk
    @0
    @16
    @4
    @5
    @0
    wcel
    #
    @14
    wa
    #
    @5
    @16
    wcel
    #
    @8
    wa
    @4
    @79
    wa
    #
    @80
    @8
    @81
    cP
    cprime
    wcel
    #
    @78
    @5
    @50
    wss
    #
    @60
    wa
    #
    vk
    vm
    weq
    #
    wb
    #
    vm
    @0
    wral
    @80
    @81
    @3
    @82
    @1
    @2
    @3
    @79
    simpl3
    cP
    cS
    pgpprm
    syl
    @4
    @78
    @14
    simprl
    #
    @81
    @86
    vm
    @0
    @81
    @58
    wa
    #
    @84
    @85
    @81
    @58
    @84
    @85
    @81
    @58
    @84
    wa
    #
    wa
    #
    @5
    @50
    wpss
    #
    wn
    @85
    @90
    @91
    @5
    chash
    cfv
    #
    @55
    clt
    wbr
    #
    @90
    @55
    @92
    cle
    wbr
    #
    @93
    wn
    #
    @90
    @55
    @12
    @92
    cle
    @90
    @11
    cr
    wss
    #
    @26
    @31
    @55
    @11
    wcel
    @55
    @12
    cle
    wbr
    @4
    @96
    @79
    @89
    @4
    @11
    cz
    cr
    @39
    zssre
    syl6ss
    ad2antrr
    @4
    @26
    @79
    @89
    @46
    ad2antrr
    @4
    @31
    @79
    @89
    @75
    ad2antrr
    @90
    @51
    @55
    @11
    @90
    @54
    @56
    @90
    @58
    @62
    @54
    @81
    @58
    @84
    simprl
    @90
    @60
    @61
    @81
    @58
    @83
    @60
    simprrr
    @90
    cH
    @5
    @50
    @90
    @7
    @8
    @81
    @9
    @89
    @4
    @78
    @9
    @13
    simprrl
    #
    adantr
    #
    simprd
    @81
    @58
    @83
    @60
    simprrl
    #
    sstrd
    jca
    @66
    sylanbrc
    #
    @57
    syl
    @90
    @42
    @54
    @51
    @11
    wcel
    @44
    @100
    @22
    @50
    cF
    fnfvelrn
    sylancr
    eqeltrrd
    vz
    vw
    @11
    @55
    suprub
    syl31anc
    @90
    @10
    @12
    @92
    @81
    @13
    @89
    @4
    @78
    @9
    @13
    simprrr
    adantr
    @90
    @5
    @22
    wcel
    #
    @10
    @92
    wceq
    @90
    @78
    @9
    @101
    @81
    @78
    @89
    @87
    adantr
    @98
    @21
    @9
    vy
    @5
    @0
    @77
    elrab
    sylanbrc
    vx
    @5
    @33
    @92
    @22
    cF
    @32
    @5
    chash
    fveq2
    pgpssslw.3
    @5
    chash
    fvex
    fvmpt
    syl
    eqtr3d
    breqtrd
    @90
    @73
    @5
    cfn
    wcel
    #
    @94
    @95
    wb
    #
    @90
    @2
    @69
    @73
    @1
    @2
    @3
    @79
    @89
    simpll2
    @58
    @69
    @81
    @84
    @71
    ad2antrl
    @74
    syl2anc
    #
    @90
    @73
    @83
    @102
    @104
    @99
    @50
    @5
    ssfi
    syl2anc
    #
    @73
    @55
    cn0
    wcel
    #
    @92
    cn0
    wcel
    #
    @103
    @102
    @50
    hashcl
    @5
    hashcl
    @106
    @55
    cr
    wcel
    @92
    cr
    wcel
    @103
    @107
    @55
    nn0re
    @92
    nn0re
    @55
    @92
    lenlt
    syl2an
    syl2an
    syl2anc
    mpbid
    @90
    @91
    @5
    @50
    csdm
    wbr
    #
    @93
    @90
    @73
    @91
    @108
    wi
    @104
    @73
    @91
    @108
    @50
    @5
    php3
    ex
    syl
    @90
    @102
    @73
    @93
    @108
    wb
    @105
    @104
    @5
    @50
    hashsdom
    syl2anc
    sylibrd
    mtod
    @90
    @91
    @85
    @90
    @83
    @91
    @85
    wo
    @99
    @5
    @50
    sspss
    sylib
    ord
    mpd
    expr
    @88
    @7
    @85
    @84
    @81
    @7
    @58
    @81
    @7
    @8
    @97
    simpld
    adantr
    @85
    @7
    @60
    @84
    @85
    @6
    @59
    cP
    cpgp
    @5
    @50
    cG
    cress
    oveq2
    breq2d
    @85
    @83
    @60
    @5
    @50
    eqimss
    biantrurd
    bitrd
    syl5ibcom
    impbid
    ralrimiva
    cP
    vm
    cG
    @5
    isslw
    syl3anbrc
    @81
    @7
    @8
    @97
    simprd
    jca
    ex
    reximdv2
    mpd
end
