include "cxp.mm"
include "cuni.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "cres.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cun.mm"
include "cmpt2.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "uneq12d.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "wcel.mm"
include "wa.mm"
include "cixp.mm"
include "cdif.mm"
include "wss.mm"
include "xp1st.mm"
include "adantl.mm"
include "ixpeq2.mm"
include "fvres.mm"
include "unieqd.mm"
include "mprg.mm"
include "cvv.mm"
include "ctop.mm"
include "wf.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "ssexd.mm"
include "fssresd.mm"
include "ptuni.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "xp2nd.mm"
include "eqcomd.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "uneqdifeq.mm"
include "mpbid.mm"
include "ixpeq1d.mm"
include "ssun2.mm"
include "eqtrd.mm"
include "undifixp.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "resixp.mm"
include "opelxpi.mm"
include "eqop.mm"
include "ad2antrl.mm"
include "wfn.mm"
include "adantrl.mm"
include "ixpfn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq2d.mm"
include "eqtr3d.mm"
include "resundi.mm"
include "syl6eq.mm"
include "uneq12.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "syl.mm"
include "adantrr.mm"
include "dffn2.mm"
include "sylib.mm"
include "res0.mm"
include "3eqtr4a.mm"
include "fresaunres1.mm"
include "fresaunres2.mm"
include "jca.mm"
include "reseq1.mm"
include "anbi12d.mm"
include "impbid.mm"
include "bitrd.mm"
include "f1ocnv2d.mm"
include "simprd.mm"

theorem ptuncnv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  assume ptunhmeo.x: |- X = U. K
  assume ptunhmeo.y: |- Y = U. L
  assume ptunhmeo.j: |- J = ( Xt_ ` F )
  assume ptunhmeo.k: |- K = ( Xt_ ` ( F |` A ) )
  assume ptunhmeo.l: |- L = ( Xt_ ` ( F |` B ) )
  assume ptunhmeo.g: |- G = ( x e. X , y e. Y |-> ( x u. y ) )
  assume ptunhmeo.c: |- ( ph -> C e. V )
  assume ptunhmeo.f: |- ( ph -> F : C --> Top )
  assume ptunhmeo.u: |- ( ph -> C = ( A u. B ) )
  assume ptunhmeo.i: |- ( ph -> ( A i^i B ) = (/) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint V z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B f
  disjoint B k
  disjoint B n
  disjoint B w
  disjoint k ph
  disjoint ph w
  disjoint C k
  disjoint C n
  disjoint F f
  disjoint F k
  disjoint F n
  disjoint J w
  disjoint K f
  disjoint K k
  disjoint L f
  disjoint L k
  disjoint V k
  disjoint X f
  disjoint X k
  disjoint X w
  disjoint Y f
  disjoint Y k
  disjoint Y w
  assert |- ( ph -> `' G = ( z e. U. J |-> <. ( z |` A ) , ( z |` B ) >. ) )

  proof
    wph
    cX
    cY
    cxp
    #
    cJ
    cuni
    #
    cG
    wf1o
    cG
    ccnv
    vz
    @1
    vz
    cv
    #
    cA
    cres
    #
    @2
    cB
    cres
    #
    cop
    #
    cmpt
    wceq
    wph
    vw
    vz
    @0
    @1
    vw
    cv
    #
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cun
    #
    @5
    cG
    cG
    vx
    vy
    cX
    cY
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cmpt2
    vw
    @0
    @9
    cmpt
    ptunhmeo.g
    vx
    vy
    vw
    cX
    cY
    @9
    @12
    @6
    @10
    @11
    cop
    wceq
    @7
    @10
    @8
    @11
    @10
    @11
    @6
    vx
    vex
    #
    vy
    vex
    #
    op1std
    @10
    @11
    @6
    @13
    @14
    op2ndd
    uneq12d
    mpt2mpt
    eqtr4i
    wph
    @6
    @0
    wcel
    #
    wa
    #
    @9
    vk
    cC
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
    @16
    @7
    vk
    cA
    @19
    cixp
    #
    wcel
    #
    @8
    vk
    cC
    cA
    cdif
    #
    @19
    cixp
    #
    wcel
    cA
    cC
    wss
    #
    @9
    @20
    wcel
    @16
    @7
    cX
    @21
    @15
    @7
    cX
    wcel
    wph
    @6
    cX
    cY
    xp1st
    adantl
    wph
    @21
    cX
    wceq
    #
    @15
    wph
    @21
    cK
    cuni
    #
    cX
    wph
    @21
    vk
    cA
    @17
    cF
    cA
    cres
    #
    cfv
    #
    cuni
    #
    cixp
    #
    @27
    @30
    @19
    wceq
    @31
    @21
    wceq
    vk
    cA
    vk
    cA
    @30
    @19
    ixpeq2
    @17
    cA
    wcel
    @29
    @18
    @17
    cA
    cF
    fvres
    unieqd
    mprg
    wph
    cA
    cvv
    wcel
    cA
    ctop
    @28
    wf
    @31
    @27
    wceq
    wph
    cA
    cC
    cV
    ptunhmeo.c
    wph
    cA
    cB
    cun
    #
    cA
    cC
    cA
    cB
    ssun1
    ptunhmeo.u
    syl5sseqr
    #
    ssexd
    wph
    cC
    ctop
    cA
    cF
    ptunhmeo.f
    @33
    fssresd
    vk
    cA
    @28
    cK
    cvv
    ptunhmeo.k
    ptuni
    syl2anc
    syl5eqr
    ptunhmeo.x
    syl6eqr
    #
    adantr
    eleqtrrd
    #
    @16
    @8
    cY
    @24
    @15
    @8
    cY
    wcel
    wph
    @6
    cX
    cY
    xp2nd
    adantl
    #
    wph
    @24
    cY
    wceq
    @15
    wph
    @24
    vk
    cB
    @19
    cixp
    #
    cY
    wph
    vk
    @23
    cB
    @19
    wph
    @32
    cC
    wceq
    #
    @23
    cB
    wceq
    #
    wph
    cC
    @32
    ptunhmeo.u
    eqcomd
    wph
    @25
    cA
    cB
    cin
    #
    c0
    wceq
    #
    @38
    @39
    wb
    @33
    ptunhmeo.i
    cA
    cB
    cC
    uneqdifeq
    syl2anc
    mpbid
    ixpeq1d
    wph
    @37
    cL
    cuni
    #
    cY
    wph
    @37
    vk
    cB
    @17
    cF
    cB
    cres
    #
    cfv
    #
    cuni
    #
    cixp
    #
    @42
    @45
    @19
    wceq
    @46
    @37
    wceq
    vk
    cB
    vk
    cB
    @45
    @19
    ixpeq2
    @17
    cB
    wcel
    @44
    @18
    @17
    cB
    cF
    fvres
    unieqd
    mprg
    wph
    cB
    cvv
    wcel
    cB
    ctop
    @43
    wf
    @46
    @42
    wceq
    wph
    cB
    cC
    cV
    ptunhmeo.c
    wph
    @32
    cB
    cC
    cB
    cA
    ssun2
    ptunhmeo.u
    syl5sseqr
    #
    ssexd
    wph
    cC
    ctop
    cB
    cF
    ptunhmeo.f
    @47
    fssresd
    vk
    cB
    @43
    cL
    cvv
    ptunhmeo.l
    ptuni
    syl2anc
    syl5eqr
    ptunhmeo.y
    syl6eqr
    #
    eqtrd
    adantr
    eleqtrrd
    wph
    @25
    @15
    @33
    adantr
    vk
    cC
    cA
    @19
    @7
    @8
    undifixp
    syl3anc
    wph
    @20
    @1
    wceq
    #
    @15
    wph
    cC
    cV
    wcel
    cC
    ctop
    cF
    wf
    @49
    ptunhmeo.c
    ptunhmeo.f
    vk
    cC
    cF
    cJ
    cV
    ptunhmeo.j
    ptuni
    syl2anc
    #
    adantr
    eleqtrd
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    cX
    wcel
    @4
    cY
    wcel
    @5
    @0
    wcel
    @52
    @3
    @21
    cX
    @52
    @25
    @2
    @20
    wcel
    #
    @3
    @21
    wcel
    wph
    @25
    @51
    @33
    adantr
    wph
    @53
    @51
    wph
    @20
    @1
    @2
    @50
    eleq2d
    biimpar
    #
    vk
    cC
    cA
    @19
    @2
    resixp
    syl2anc
    wph
    @26
    @51
    @34
    adantr
    eleqtrd
    @52
    @4
    @37
    cY
    @52
    cB
    cC
    wss
    #
    @53
    @4
    @37
    wcel
    wph
    @55
    @51
    @47
    adantr
    @54
    vk
    cC
    cB
    @19
    @2
    resixp
    syl2anc
    wph
    @37
    cY
    wceq
    #
    @51
    @48
    adantr
    eleqtrd
    @3
    @4
    cX
    cY
    opelxpi
    syl2anc
    wph
    @15
    @51
    wa
    #
    wa
    #
    @6
    @5
    wceq
    #
    @7
    @3
    wceq
    #
    @8
    @4
    wceq
    #
    wa
    #
    @2
    @9
    wceq
    #
    @15
    @59
    @62
    wb
    wph
    @51
    @6
    @3
    @4
    cX
    cY
    eqop
    ad2antrl
    @58
    @62
    @63
    @58
    @63
    @62
    @2
    @3
    @4
    cun
    #
    wceq
    @58
    @2
    @2
    @32
    cres
    #
    @64
    @58
    @2
    cC
    cres
    #
    @2
    @65
    @58
    @53
    @2
    cC
    wfn
    @66
    @2
    wceq
    wph
    @51
    @53
    @15
    @54
    adantrl
    vk
    cC
    @19
    @2
    ixpfn
    cC
    @2
    fnresdm
    3syl
    wph
    @66
    @65
    wceq
    @57
    wph
    cC
    @32
    @2
    ptunhmeo.u
    reseq2d
    adantr
    eqtr3d
    @2
    cA
    cB
    resundi
    syl6eq
    @62
    @9
    @64
    @2
    @7
    @3
    @8
    @4
    uneq12
    eqeq2d
    syl5ibrcom
    @58
    @62
    @63
    @7
    @9
    cA
    cres
    #
    wceq
    #
    @8
    @9
    cB
    cres
    #
    wceq
    #
    wa
    @58
    @68
    @70
    @58
    @67
    @7
    @58
    cA
    cvv
    @7
    wf
    #
    cB
    cvv
    @8
    wf
    #
    @7
    @40
    cres
    #
    @8
    @40
    cres
    #
    wceq
    #
    @67
    @7
    wceq
    @58
    @7
    cA
    wfn
    #
    @71
    wph
    @15
    @76
    @51
    @16
    @22
    @76
    @35
    vk
    cA
    @19
    @7
    ixpfn
    syl
    adantrr
    cA
    @7
    dffn2
    sylib
    #
    @58
    @8
    cB
    wfn
    #
    @72
    wph
    @15
    @78
    @51
    @16
    @8
    @37
    wcel
    @78
    @16
    @8
    cY
    @37
    @36
    wph
    @56
    @15
    @48
    adantr
    eleqtrrd
    vk
    cB
    @19
    @8
    ixpfn
    syl
    adantrr
    cB
    @8
    dffn2
    sylib
    #
    @58
    @7
    c0
    cres
    #
    @8
    c0
    cres
    #
    @73
    @74
    @80
    c0
    @81
    @7
    res0
    @8
    res0
    eqtr4i
    @58
    @40
    c0
    @7
    wph
    @41
    @57
    ptunhmeo.i
    adantr
    #
    reseq2d
    @58
    @40
    c0
    @8
    @82
    reseq2d
    3eqtr4a
    #
    cA
    cB
    cvv
    @7
    @8
    fresaunres1
    syl3anc
    eqcomd
    @58
    @69
    @8
    @58
    @71
    @72
    @75
    @69
    @8
    wceq
    @77
    @79
    @83
    cA
    cB
    cvv
    @7
    @8
    fresaunres2
    syl3anc
    eqcomd
    jca
    @63
    @60
    @68
    @61
    @70
    @63
    @3
    @67
    @7
    @2
    @9
    cA
    reseq1
    eqeq2d
    @63
    @4
    @69
    @8
    @2
    @9
    cB
    reseq1
    eqeq2d
    anbi12d
    syl5ibrcom
    impbid
    bitrd
    f1ocnv2d
    simprd
end
