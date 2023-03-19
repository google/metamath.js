include "wcel.mm"
include "cringc.mm"
include "cfv.mm"
include "csubc.mm"
include "chomf.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "ccid.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "crg.mm"
include "cin.mm"
include "wss.mm"
include "eleq1.mm"
include "vtoclri.mm"
include "ssriv.mm"
include "sslin.mm"
include "mp1i.mm"
include "syl5eqss.mm"
include "crh.mm"
include "chom.mm"
include "ssid.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "srhmsubclem2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "ringchom.mm"
include "syl5sseqr.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq12.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "homfval.mm"
include "3sstr4d.mm"
include "ralrimivva.mm"
include "cxp.mm"
include "wfn.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "homffn.mm"
include "id.mm"
include "ringcbas.mm"
include "eqcomd.mm"
include "sqxpeqd.mm"
include "fneq2d.mm"
include "mpbiri.mm"
include "inex1g.mm"
include "isssc.mm"
include "mpbir2and.mm"
include "cid.mm"
include "cres.mm"
include "elin2.mm"
include "sylbi.mm"
include "idrhm.mm"
include "syl.mm"
include "ringcid.mm"
include "simpr.mm"
include "3eltr4d.mm"
include "ccat.mm"
include "ringccat.mm"
include "ad3antrrr.mm"
include "adantr.mm"
include "ad2ant2r.mm"
include "ad2ant2rl.mm"
include "wi.mm"
include "anim12i.mm"
include "jca.mm"
include "srhmsubclem3.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "adantlr.mm"
include "biimpd.mm"
include "adantld.mm"
include "imp.mm"
include "catcocl.mm"
include "eleqtrrd.mm"
include "ralrimiva.mm"
include "issubc2.mm"

theorem srhmsubc
  let cC: class C
  let cS: class S
  let cU: class U
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume srhmsubc.s: |- A. r e. S r e. Ring
  assume srhmsubc.c: |- C = ( U i^i S )
  assume srhmsubc.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )

  disjoint S r
  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint X r
  disjoint X s
  disjoint Y r
  disjoint Y s
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S x
  disjoint U f
  disjoint U g
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint k x
  assert |- ( U e. V -> J e. ( Subcat ` ( RingCat ` U ) ) )

  proof
    cU
    cV
    wcel
    #
    cJ
    cU
    cringc
    cfv
    #
    csubc
    cfv
    wcel
    cJ
    @1
    chomf
    cfv
    #
    cssc
    wbr
    #
    vx
    cv
    #
    @1
    ccid
    cfv
    #
    cfv
    #
    @4
    @4
    cJ
    co
    #
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    @4
    vy
    cv
    #
    cop
    vz
    cv
    #
    @1
    cco
    cfv
    #
    co
    co
    #
    @4
    @12
    cJ
    co
    #
    wcel
    #
    vg
    @11
    @12
    cJ
    co
    #
    wral
    vf
    @4
    @11
    cJ
    co
    #
    wral
    #
    vz
    cC
    wral
    vy
    cC
    wral
    #
    wa
    #
    vx
    cC
    wral
    @0
    @3
    cC
    cU
    crg
    cin
    #
    wss
    @18
    @4
    @11
    @2
    co
    #
    wss
    #
    vy
    cC
    wral
    vx
    cC
    wral
    @0
    cC
    cU
    cS
    cin
    #
    @22
    srhmsubc.c
    cS
    crg
    wss
    @25
    @22
    wss
    @0
    vx
    cS
    crg
    vr
    cv
    #
    crg
    wcel
    @4
    crg
    wcel
    #
    vr
    @4
    cS
    @26
    @4
    crg
    eleq1
    srhmsubc.s
    vtoclri
    #
    ssriv
    cS
    crg
    cU
    sslin
    mp1i
    syl5eqss
    @0
    @24
    vx
    vy
    cC
    cC
    @0
    @4
    cC
    wcel
    #
    @11
    cC
    wcel
    #
    wa
    #
    wa
    #
    @4
    @11
    crh
    co
    #
    @4
    @11
    @1
    chom
    cfv
    #
    co
    #
    @18
    @23
    @32
    @33
    @33
    @35
    @33
    ssid
    @32
    @1
    cbs
    cfv
    #
    @1
    cU
    @34
    cV
    @4
    @11
    @1
    eqid
    #
    @36
    eqid
    #
    @0
    @31
    simpl
    @34
    eqid
    #
    @0
    @29
    @4
    @36
    wcel
    #
    @30
    cC
    cS
    cU
    cV
    @4
    vr
    srhmsubc.s
    srhmsubc.c
    srhmsubclem2
    #
    adantrr
    #
    @0
    @30
    @11
    @36
    wcel
    #
    @29
    cC
    cS
    cU
    cV
    @11
    vr
    srhmsubc.s
    srhmsubc.c
    srhmsubclem2
    #
    adantrl
    #
    ringchom
    syl5sseqr
    @32
    vr
    vs
    @4
    @11
    cC
    cC
    @26
    vs
    cv
    #
    crh
    co
    #
    @33
    cJ
    cvv
    cJ
    vr
    vs
    cC
    cC
    @47
    cmpt2
    wceq
    #
    @32
    srhmsubc.j
    a1i
    @26
    @4
    wceq
    #
    @46
    @11
    wceq
    wa
    @47
    @33
    wceq
    @32
    @26
    @4
    @46
    @11
    crh
    oveq12
    adantl
    @0
    @29
    @30
    simprl
    @0
    @29
    @30
    simprr
    @32
    @4
    @11
    crh
    ovexd
    ovmpt2d
    @32
    @36
    @1
    @2
    @34
    @4
    @11
    @2
    eqid
    #
    @38
    @39
    @42
    @45
    homfval
    3sstr4d
    ralrimivva
    @0
    vx
    vy
    cC
    @22
    cJ
    @2
    cvv
    cJ
    cC
    cC
    cxp
    wfn
    @0
    vr
    vs
    cC
    cC
    @47
    cJ
    srhmsubc.j
    @26
    @46
    crh
    ovex
    fnmpt2i
    a1i
    #
    @0
    @2
    @22
    @22
    cxp
    #
    wfn
    @2
    @36
    @36
    cxp
    #
    wfn
    @36
    @1
    @2
    @50
    @38
    homffn
    @0
    @52
    @53
    @2
    @0
    @22
    @36
    @0
    @36
    @22
    @0
    @36
    @1
    cU
    cV
    @37
    @38
    @0
    id
    ringcbas
    eqcomd
    sqxpeqd
    fneq2d
    mpbiri
    cU
    crg
    cV
    inex1g
    isssc
    mpbir2and
    @0
    @21
    vx
    cC
    @0
    @29
    wa
    #
    @8
    @20
    @54
    cid
    @4
    cbs
    cfv
    #
    cres
    #
    @4
    @4
    crh
    co
    #
    @6
    @7
    @54
    @27
    @56
    @57
    wcel
    @29
    @27
    @0
    @29
    @4
    cU
    wcel
    #
    @4
    cS
    wcel
    #
    wa
    @27
    @4
    cU
    cS
    cC
    srhmsubc.c
    elin2
    @59
    @27
    @58
    @28
    adantl
    sylbi
    adantl
    @55
    @4
    @55
    eqid
    #
    idrhm
    syl
    @54
    @36
    @1
    @55
    cU
    @5
    cV
    @4
    @37
    @38
    @5
    eqid
    #
    @0
    @29
    simpl
    #
    @41
    @60
    ringcid
    @54
    vr
    vs
    @4
    @4
    cC
    cC
    @47
    @57
    cJ
    cvv
    @48
    @54
    srhmsubc.j
    a1i
    @49
    @46
    @4
    wceq
    wa
    @47
    @57
    wceq
    @54
    @26
    @4
    @46
    @4
    crh
    oveq12
    adantl
    @0
    @29
    simpr
    #
    @63
    @54
    @4
    @4
    crh
    ovexd
    ovmpt2d
    3eltr4d
    @54
    @19
    vy
    vz
    cC
    cC
    @54
    @30
    @12
    cC
    wcel
    #
    wa
    #
    wa
    #
    @16
    vf
    vg
    @18
    @17
    @66
    @10
    @18
    wcel
    #
    @9
    @17
    wcel
    #
    wa
    #
    wa
    #
    @14
    @4
    @12
    crh
    co
    #
    @15
    @70
    @14
    @4
    @12
    @34
    co
    #
    @71
    @70
    @36
    @1
    @13
    @10
    @9
    @34
    @4
    @11
    @12
    @38
    @39
    @13
    eqid
    #
    @0
    @1
    ccat
    wcel
    @29
    @65
    @69
    @1
    cU
    cV
    @37
    ringccat
    #
    ad3antrrr
    @66
    @40
    @69
    @54
    @40
    @65
    @41
    adantr
    #
    adantr
    @66
    @43
    @69
    @0
    @30
    @43
    @29
    @64
    @44
    ad2ant2r
    adantr
    @66
    @12
    @36
    wcel
    #
    @69
    @0
    @64
    @76
    @29
    @30
    cC
    cS
    cU
    cV
    @12
    vr
    srhmsubc.s
    srhmsubc.c
    srhmsubclem2
    ad2ant2rl
    #
    adantr
    @69
    @66
    @10
    @35
    wcel
    #
    @67
    @66
    @78
    wi
    @68
    @66
    @67
    @78
    @66
    @18
    @35
    @10
    @66
    @32
    @18
    @35
    wceq
    @66
    @0
    @31
    @54
    @0
    @65
    @62
    adantr
    #
    @54
    @29
    @65
    @30
    @63
    @30
    @64
    simpl
    anim12i
    jca
    cC
    cS
    cU
    cJ
    cV
    @4
    @11
    vs
    vr
    srhmsubc.s
    srhmsubc.c
    srhmsubc.j
    srhmsubclem3
    syl
    eleq2d
    biimpcd
    adantr
    impcom
    @66
    @69
    @9
    @11
    @12
    @34
    co
    #
    wcel
    #
    @66
    @68
    @81
    @67
    @66
    @68
    @81
    @66
    @17
    @80
    @9
    @0
    @65
    @17
    @80
    wceq
    @29
    cC
    cS
    cU
    cJ
    cV
    @11
    @12
    vs
    vr
    srhmsubc.s
    srhmsubc.c
    srhmsubc.j
    srhmsubclem3
    adantlr
    eleq2d
    biimpd
    adantld
    imp
    catcocl
    @66
    @71
    @72
    wceq
    @69
    @66
    @72
    @71
    @66
    @36
    @1
    cU
    @34
    cV
    @4
    @12
    @37
    @38
    @79
    @39
    @75
    @77
    ringchom
    eqcomd
    adantr
    eleqtrrd
    @66
    @15
    @71
    wceq
    @69
    @66
    vr
    vs
    @4
    @12
    cC
    cC
    @47
    @71
    cJ
    cvv
    @48
    @66
    srhmsubc.j
    a1i
    @49
    @46
    @12
    wceq
    wa
    @47
    @71
    wceq
    @66
    @26
    @4
    @46
    @12
    crh
    oveq12
    adantl
    @54
    @29
    @65
    @63
    adantr
    @54
    @30
    @64
    simprr
    @66
    @4
    @12
    crh
    ovexd
    ovmpt2d
    adantr
    eleqtrrd
    ralrimivva
    ralrimivva
    jca
    ralrimiva
    @0
    vx
    vy
    vz
    @1
    cC
    @13
    @5
    vf
    vg
    @2
    cJ
    @50
    @61
    @73
    @74
    @51
    issubc2
    mpbir2and
end
