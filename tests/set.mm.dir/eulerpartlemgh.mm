include "cin.mm"
include "wcel.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cfv.mm"
include "cbits.mm"
include "wrex.mm"
include "cn.mm"
include "crab.mm"
include "cn0.mm"
include "cxp.mm"
include "wf1.mm"
include "wss.mm"
include "oddpwdc.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "ccnv.mm"
include "csn.mm"
include "ciun.mm"
include "iunss.mm"
include "inss2.mm"
include "sseli.mm"
include "snssd.mm"
include "bitsss.mm"
include "xpss12.mm"
include "sylancl.mm"
include "mprgbir.mm"
include "eqsstri.mm"
include "f1ores.mm"
include "mp2an.mm"
include "wb.mm"
include "wa.mm"
include "simpr.mm"
include "2nn.mm"
include "a1i.mm"
include "adantl.mm"
include "nnexpcld.mm"
include "simplr.mm"
include "nnmulcld.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "rexlimdva.mm"
include "pm4.71rd.mm"
include "wn.mm"
include "c0.mm"
include "rex0.mm"
include "cc0.mm"
include "wo.mm"
include "wi.mm"
include "wf.mm"
include "wfn.mm"
include "cmap.mm"
include "cfn.mm"
include "eulerpartlemt0.mm"
include "simp1bi.mm"
include "elmapi.mm"
include "syl.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mtbid.mm"
include "imnan.mm"
include "sylibr.mm"
include "mpd.mm"
include "ffvelrnd.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"
include "fveq2d.mm"
include "0bits.mm"
include "syl6eq.mm"
include "rexeqdv.mm"
include "mtbiri.mm"
include "ex.mm"
include "con4d.mm"
include "impr.mm"
include "cdif.mm"
include "eldif.mm"
include "eulerpartlemf.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "elind.mm"
include "simprr.mm"
include "jca.mm"
include "reximdv2.mm"
include "cdvds.mm"
include "wbr.mm"
include "ssrab2.mm"
include "sstri.mm"
include "ssrexv.mm"
include "mp1i.mm"
include "impbid.mm"
include "bitr3d.mm"
include "weq.mm"
include "eqeq2.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "imaeq2i.mm"
include "imaiun.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eliun.mm"
include "f1ofn.mm"
include "snssi.mm"
include "ovelimab.mm"
include "sylancr.mm"
include "vex.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rexsn.mm"
include "syl6bb.mm"
include "cop.mm"
include "df-ov.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "bitr3i.mm"
include "opelxpi.mm"
include "c2nd.mm"
include "c1st.mm"
include "oddpwdcv.mm"
include "op2nd.mm"
include "oveq2i.mm"
include "op1st.mm"
include "oveq12i.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"
include "sylan2.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "rexbiia.mm"
include "3bitri.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"
include "f1oeq3.mm"
include "mpbii.mm"

theorem eulerpartlemgh
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  let vp: setvar p
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )
  assume eulerpart.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpart.t: |- T = { f e. ( NN0 ^m NN ) | ( `' f " NN ) C_ J }
  assume eulerpart.g: |- G = ( o e. ( T i^i R ) |-> ( ( _Ind ` NN ) ` ( F " ( M ` ( bits o. ( o |` J ) ) ) ) ) )
  assume eulerpartlemgh.1: |- U = U_ t e. ( ( `' A " NN ) i^i J ) ( { t } X. ( bits ` ( A ` t ) ) )

  disjoint t z
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint A f
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint A g
  disjoint k n
  disjoint k t
  disjoint A k
  disjoint n t
  disjoint A n
  disjoint A t
  disjoint J f
  disjoint J n
  disjoint J t
  disjoint N f
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint O n
  disjoint O t
  disjoint P g
  disjoint P k
  disjoint R f
  disjoint R k
  disjoint R n
  disjoint R t
  disjoint T n
  disjoint T t
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint f m
  disjoint f x
  disjoint g m
  disjoint g x
  disjoint k m
  disjoint k x
  disjoint m n
  disjoint m t
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A x
  disjoint F n
  disjoint F t
  disjoint F x
  disjoint f y
  disjoint n y
  disjoint J x
  disjoint J y
  disjoint P t
  disjoint f p
  disjoint g p
  disjoint k p
  disjoint m p
  disjoint n p
  disjoint p t
  disjoint p x
  disjoint A p
  disjoint F p
  disjoint O p
  disjoint R p
  disjoint N p
  disjoint U p
  disjoint T p
  assert |- ( A e. ( T i^i R ) -> ( F |` U ) : U -1-1-onto-> { m e. NN | E. t e. NN E. n e. ( bits ` ( A ` t ) ) ( ( 2 ^ n ) x. t ) = m } )

  proof
    cA
    cT
    cR
    cin
    wcel
    #
    cU
    cF
    cU
    cima
    #
    cF
    cU
    cres
    #
    wf1o
    #
    cU
    c2
    vn
    cv
    #
    cexp
    co
    #
    vt
    cv
    #
    cmul
    co
    #
    vm
    cv
    #
    wceq
    #
    vn
    @6
    cA
    cfv
    #
    cbits
    cfv
    #
    wrex
    vt
    cn
    wrex
    #
    vm
    cn
    crab
    #
    @2
    wf1o
    #
    cJ
    cn0
    cxp
    #
    cn
    cF
    wf1
    #
    cU
    @15
    wss
    @3
    @15
    cn
    cF
    wf1o
    #
    @16
    vx
    vy
    vz
    cF
    cJ
    eulerpart.j
    eulerpart.f
    oddpwdc
    #
    @15
    cn
    cF
    f1of1
    ax-mp
    cU
    vt
    cA
    ccnv
    cn
    cima
    #
    cJ
    cin
    #
    @6
    csn
    #
    @11
    cxp
    #
    ciun
    #
    @15
    eulerpartlemgh.1
    @23
    @15
    wss
    @22
    @15
    wss
    #
    vt
    @20
    vt
    @20
    @22
    @15
    iunss
    @6
    @20
    wcel
    #
    @21
    cJ
    wss
    #
    @11
    cn0
    wss
    #
    @24
    @25
    @6
    cJ
    @20
    cJ
    @6
    @19
    cJ
    inss2
    #
    sseli
    #
    snssd
    @10
    bitsss
    #
    @21
    cJ
    @11
    cn0
    xpss12
    #
    sylancl
    mprgbir
    eqsstri
    @15
    cn
    cU
    cF
    f1ores
    mp2an
    @0
    @1
    @13
    wceq
    @3
    @14
    wb
    @0
    vp
    @1
    @13
    @0
    vp
    cv
    #
    cn
    wcel
    #
    @7
    @32
    wceq
    #
    vn
    @11
    wrex
    #
    vt
    cn
    wrex
    #
    wa
    #
    @35
    vt
    @20
    wrex
    #
    @32
    @13
    wcel
    #
    @32
    @1
    wcel
    #
    @0
    @36
    @37
    @38
    @0
    @36
    @33
    @0
    @35
    @33
    vt
    cn
    @0
    @6
    cn
    wcel
    #
    wa
    #
    @34
    @33
    vn
    @11
    @42
    @4
    @11
    wcel
    #
    @34
    @33
    @42
    @43
    wa
    #
    @34
    wa
    @7
    @32
    cn
    @44
    @34
    simpr
    @44
    @7
    cn
    wcel
    @34
    @44
    @5
    @6
    @44
    c2
    @4
    c2
    cn
    wcel
    @44
    2nn
    a1i
    @43
    @4
    cn0
    wcel
    #
    @42
    @11
    cn0
    @4
    @30
    sseli
    #
    adantl
    nnexpcld
    @0
    @41
    @43
    simplr
    nnmulcld
    adantr
    eqeltrrd
    exp31
    rexlimdv
    rexlimdva
    pm4.71rd
    @0
    @36
    @38
    @0
    @35
    @35
    vt
    cn
    @20
    @0
    @41
    @35
    wa
    #
    @25
    @35
    wa
    @0
    @47
    wa
    #
    @25
    @35
    @48
    @19
    cJ
    @6
    @0
    @41
    @35
    @6
    @19
    wcel
    #
    @42
    @49
    @35
    @42
    @49
    wn
    #
    @35
    wn
    #
    @42
    @50
    wa
    #
    @35
    @34
    vn
    c0
    wrex
    #
    @34
    vn
    rex0
    #
    @52
    @34
    vn
    @11
    c0
    @52
    @11
    cc0
    cbits
    cfv
    #
    c0
    @52
    @10
    cc0
    cbits
    @52
    @10
    cn
    wcel
    #
    wn
    #
    @56
    @10
    cc0
    wceq
    #
    wo
    #
    @58
    @52
    @41
    @57
    @0
    @41
    @50
    simplr
    #
    @52
    @41
    @56
    wa
    #
    wn
    @41
    @57
    wi
    @52
    @49
    @61
    @42
    @50
    simpr
    @52
    cn
    cn0
    cA
    wf
    #
    cA
    cn
    wfn
    @49
    @61
    wb
    @0
    @62
    @41
    @50
    @0
    cA
    cn0
    cn
    cmap
    co
    wcel
    #
    @62
    @0
    @63
    @19
    cfn
    wcel
    @19
    cJ
    wss
    vx
    vy
    vz
    cA
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    simp1bi
    cA
    cn0
    cn
    elmapi
    syl
    ad2antrr
    #
    cn
    cn0
    cA
    ffn
    cn
    @6
    cn
    cA
    elpreima
    3syl
    mtbid
    @41
    @56
    imnan
    sylibr
    mpd
    @52
    @10
    cn0
    wcel
    @59
    @52
    cn
    cn0
    @6
    cA
    @64
    @60
    ffvelrnd
    @10
    elnn0
    sylib
    @56
    @58
    orel1
    sylc
    fveq2d
    0bits
    syl6eq
    rexeqdv
    mtbiri
    ex
    con4d
    impr
    @0
    @41
    @35
    @6
    cJ
    wcel
    #
    @42
    @65
    @35
    @42
    @65
    wn
    #
    @51
    @42
    @66
    wa
    #
    @35
    @53
    @54
    @67
    @34
    vn
    @11
    c0
    @67
    @11
    @55
    c0
    @67
    @10
    cc0
    cbits
    @0
    @41
    @66
    @58
    @41
    @66
    wa
    @0
    @6
    cn
    cJ
    cdif
    wcel
    @58
    @6
    cn
    cJ
    eldif
    vx
    vy
    vz
    vt
    cA
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemf
    sylan2br
    anassrs
    fveq2d
    0bits
    syl6eq
    rexeqdv
    mtbiri
    ex
    con4d
    impr
    elind
    @0
    @41
    @35
    simprr
    jca
    ex
    reximdv2
    @20
    cn
    wss
    @38
    @36
    wi
    @0
    @20
    cJ
    cn
    @28
    cJ
    c2
    vz
    cv
    cdvds
    wbr
    wn
    #
    vz
    cn
    crab
    cn
    eulerpart.j
    @68
    vz
    cn
    ssrab2
    eqsstri
    sstri
    @35
    vt
    @20
    cn
    ssrexv
    mp1i
    impbid
    bitr3d
    @39
    @37
    wb
    @0
    @12
    @36
    vm
    @32
    cn
    vm
    vp
    weq
    @9
    @34
    vt
    vn
    cn
    @11
    @8
    @32
    @7
    eqeq2
    2rexbidv
    elrab
    a1i
    @40
    @38
    wb
    @0
    @40
    @32
    vt
    @20
    cF
    @22
    cima
    #
    ciun
    #
    wcel
    @32
    @69
    wcel
    #
    vt
    @20
    wrex
    @38
    @1
    @70
    @32
    @1
    cF
    @23
    cima
    @70
    cU
    @23
    cF
    eulerpartlemgh.1
    imaeq2i
    vt
    cF
    @20
    @22
    imaiun
    eqtri
    eleq2i
    vt
    @32
    @20
    @69
    eliun
    @71
    @35
    vt
    @20
    @25
    @65
    @71
    @35
    wb
    @29
    @65
    @71
    @32
    @6
    @4
    cF
    co
    #
    wceq
    #
    vn
    @11
    wrex
    #
    @35
    @65
    @71
    @32
    vx
    cv
    #
    @4
    cF
    co
    #
    wceq
    #
    vn
    @11
    wrex
    #
    vx
    @21
    wrex
    #
    @74
    @65
    cF
    @15
    wfn
    #
    @24
    @71
    @79
    wb
    @17
    @80
    @18
    @15
    cn
    cF
    f1ofn
    ax-mp
    @65
    @26
    @27
    @24
    @6
    cJ
    snssi
    @30
    @31
    sylancl
    vx
    vn
    @15
    @21
    @11
    @32
    cF
    ovelimab
    sylancr
    @78
    @74
    vx
    @6
    vt
    vex
    #
    vx
    vt
    weq
    #
    @77
    @73
    vn
    @11
    @82
    @76
    @72
    @32
    @75
    @6
    @4
    cF
    oveq1
    eqeq2d
    rexbidv
    rexsn
    syl6bb
    @65
    @73
    @34
    vn
    @11
    @43
    @65
    @45
    @73
    @34
    wb
    @46
    @73
    @6
    @4
    cop
    #
    cF
    cfv
    #
    @32
    wceq
    #
    @65
    @45
    wa
    #
    @34
    @85
    @72
    @32
    wceq
    @73
    @72
    @84
    @32
    @6
    @4
    cF
    df-ov
    eqeq1i
    @72
    @32
    eqcom
    bitr3i
    @86
    @84
    @7
    @32
    @86
    @83
    @15
    wcel
    #
    @84
    @7
    wceq
    @6
    @4
    cJ
    cn0
    opelxpi
    @87
    @84
    c2
    @83
    c2nd
    cfv
    #
    cexp
    co
    #
    @83
    c1st
    cfv
    #
    cmul
    co
    @7
    vx
    vy
    vz
    cF
    cJ
    @83
    eulerpart.j
    eulerpart.f
    oddpwdcv
    @89
    @5
    @90
    @6
    cmul
    @88
    @4
    c2
    cexp
    @6
    @4
    @81
    vn
    vex
    #
    op2nd
    oveq2i
    @6
    @4
    @81
    @91
    op1st
    oveq12i
    syl6eq
    syl
    eqeq1d
    syl5bbr
    sylan2
    rexbidva
    bitrd
    syl
    rexbiia
    3bitri
    a1i
    3bitr4rd
    eqrdv
    @1
    @13
    cU
    @2
    f1oeq3
    syl
    mpbii
end
