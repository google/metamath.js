include "cv.mm"
include "ccnv.mm"
include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "crab.mm"
include "cvv.mm"
include "cfn.mm"
include "ccrd.mm"
include "com.mm"
include "cint.mm"
include "cif.mm"
include "cmpt2.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "cin.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "copab.mm"
include "cdm.mm"
include "cuni.mm"
include "cmap.mm"
include "ciun.mm"
include "ccom.mm"
include "wf1.mm"
include "wf1o.mm"
include "cep.mm"
include "wiso.mm"
include "vex.mm"
include "w3a.mm"
include "cdom.mm"
include "wbr.mm"
include "simprl3.mm"
include "sylan2b.mm"
include "oiiso.mm"
include "sylancr.mm"
include "isof1o.mm"
include "syl.mm"
include "cpw.mm"
include "char.mm"
include "wi.mm"
include "con0.mm"
include "oion.mm"
include "ax-mp.mm"
include "a1i.mm"
include "cen.mm"
include "oien.mm"
include "adantr.mm"
include "omex.mm"
include "ovex.mm"
include "iunex.mm"
include "f1dmex.mm"
include "sylancl.mm"
include "pwexb.mm"
include "sylibr.mm"
include "simprl1.mm"
include "ssdomg.mm"
include "sylc.mm"
include "csdm.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "3syl.mm"
include "domtr.mm"
include "syl2anc.mm"
include "endomtr.mm"
include "elharval.mm"
include "sylanbrc.mm"
include "cardom.mm"
include "simprr.mm"
include "ensymd.mm"
include "domentr.mm"
include "wb.mm"
include "omelon.mm"
include "onenon.mm"
include "mp1i.mm"
include "carddom2.mm"
include "mpbird.mm"
include "syl5eqssr.mm"
include "cardonle.mm"
include "sstrd.mm"
include "sseq2.mm"
include "fveq2.mm"
include "f1oeq1.mm"
include "xpeq12.mm"
include "anidms.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "3bitrd.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "f1oco.mm"
include "cop.mm"
include "cmpt.mm"
include "wf.mm"
include "f1of.mm"
include "feqmptd.mm"
include "mpbid.mm"
include "xpf1o.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "cres.mm"
include "f1ssres.mm"
include "f1f1orn.mm"
include "feqresmpt.mm"
include "cid.mm"
include "mptresid.mm"
include "f1oi.mm"
include "mpbiri.mm"
include "f1f.mm"
include "frn.mm"
include "xpss1.mm"
include "4syl.mm"
include "f1ss.mm"
include "f1co.mm"
include "c0.mm"
include "peano1.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "fseqenlem2.mm"
include "f1eq1.mm"
include "eqid.mm"
include "fpwwe2cbv.mm"
include "pwfseqlem4.mm"

theorem pwfseqlem5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cO: class O
  let cX: class X
  let vr: setvar r
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  assume pwfseqlem5.g: |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) )
  assume pwfseqlem5.x: |- ( ph -> X C_ A )
  assume pwfseqlem5.h: |- ( ph -> H : _om -1-1-onto-> X )
  assume pwfseqlem5.ps: |- ( ps <-> ( ( t C_ A /\ r C_ ( t X. t ) /\ r We t ) /\ _om ~<_ t ) )
  assume pwfseqlem5.n: |- ( ph -> A. b e. ( har ` ~P A ) ( _om C_ b -> ( N ` b ) : ( b X. b ) -1-1-onto-> b ) )
  assume pwfseqlem5.o: |- O = OrdIso ( r , t )
  assume pwfseqlem5.t: |- T = ( u e. dom O , v e. dom O |-> <. ( O ` u ) , ( O ` v ) >. )
  assume pwfseqlem5.p: |- P = ( ( O o. ( N ` dom O ) ) o. `' T )
  assume pwfseqlem5.s: |- S = seqom ( ( k e. _V , f e. _V |-> ( x e. ( t ^m suc k ) |-> ( ( f ` ( x |` k ) ) P ( x ` k ) ) ) ) , { <. (/) , ( O ` (/) ) >. } )
  assume pwfseqlem5.q: |- Q = ( y e. U_ n e. _om ( t ^m n ) |-> <. dom y , ( ( S ` dom y ) ` y ) >. )
  assume pwfseqlem5.i: |- I = ( x e. _om , y e. t |-> <. ( O ` x ) , y >. )
  assume pwfseqlem5.k: |- K = ( ( P o. I ) o. Q )

  disjoint b n
  disjoint G b
  disjoint G n
  disjoint b r
  disjoint b t
  disjoint H b
  disjoint r t
  disjoint H r
  disjoint H t
  disjoint f k
  disjoint f x
  disjoint P f
  disjoint k x
  disjoint P k
  disjoint P x
  disjoint b f
  disjoint b k
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint f n
  disjoint f r
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint K b
  disjoint K n
  disjoint N b
  disjoint k ps
  disjoint n ps
  disjoint ps x
  disjoint ps y
  disjoint S n
  disjoint S y
  disjoint A b
  disjoint A n
  disjoint A r
  disjoint A t
  disjoint O b
  disjoint O u
  disjoint O v
  disjoint O x
  disjoint O y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a z
  disjoint G a
  disjoint b c
  disjoint b d
  disjoint b i
  disjoint b j
  disjoint b m
  disjoint b s
  disjoint b w
  disjoint b z
  disjoint c d
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c w
  disjoint c z
  disjoint G c
  disjoint d i
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d s
  disjoint d w
  disjoint d z
  disjoint G d
  disjoint i j
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i w
  disjoint i z
  disjoint G i
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint G j
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m z
  disjoint G m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint s w
  disjoint s z
  disjoint G s
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint a r
  disjoint a t
  disjoint H a
  disjoint c r
  disjoint c t
  disjoint H c
  disjoint d r
  disjoint d t
  disjoint H d
  disjoint j r
  disjoint j t
  disjoint H j
  disjoint m r
  disjoint m t
  disjoint H m
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s t
  disjoint H s
  disjoint t w
  disjoint t z
  disjoint H w
  disjoint H z
  disjoint a f
  disjoint a k
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint c f
  disjoint c k
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d k
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f s
  disjoint f w
  disjoint f z
  disjoint i k
  disjoint i r
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k s
  disjoint k w
  disjoint k z
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint x z
  disjoint y z
  disjoint a ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint K a
  disjoint K c
  disjoint K d
  disjoint K i
  disjoint K j
  disjoint K m
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint ps z
  disjoint A a
  disjoint A c
  disjoint A d
  disjoint A s
  disjoint A w
  disjoint A z
  assert |- -. ph

  proof
    wph
    wps
    vt
    vz
    vi
    vw
    cA
    vi
    cv
    #
    cK
    ccnv
    cfv
    #
    cG
    crn
    wcel
    @0
    @1
    cG
    ccnv
    cfv
    wcel
    wn
    wa
    vi
    vt
    cv
    #
    crab
    cG
    cfv
    #
    vn
    vt
    vr
    cvv
    cvv
    @2
    cfn
    wcel
    @2
    ccrd
    cfv
    cH
    cfv
    vz
    cv
    @3
    cfv
    @2
    wcel
    wn
    vz
    com
    crab
    cint
    @3
    cfv
    cif
    cmpt2
    #
    cG
    cH
    cK
    vc
    cv
    #
    cA
    wss
    vd
    cv
    #
    @5
    @5
    cxp
    wss
    wa
    @5
    @6
    wwe
    vj
    cv
    #
    @6
    @7
    @7
    cxp
    cin
    @4
    co
    vm
    cv
    #
    wceq
    vj
    @6
    ccnv
    @8
    csn
    cima
    wsbc
    vm
    @5
    wral
    wa
    wa
    vc
    vd
    copab
    #
    cX
    @9
    cdm
    cuni
    #
    vs
    vr
    va
    vb
    pwfseqlem5.g
    pwfseqlem5.x
    pwfseqlem5.h
    pwfseqlem5.ps
    wph
    wps
    wa
    #
    vn
    com
    @2
    vn
    cv
    #
    cmap
    co
    ciun
    #
    @2
    cP
    cI
    ccom
    #
    cQ
    ccom
    #
    wf1
    #
    @13
    @2
    cK
    wf1
    #
    @11
    com
    @2
    cxp
    #
    @2
    @14
    wf1
    #
    @13
    @18
    cQ
    wf1
    @16
    @11
    @2
    @2
    cxp
    #
    @2
    cP
    wf1
    #
    @18
    @20
    cI
    wf1
    #
    @19
    @11
    @20
    @2
    cP
    wf1o
    #
    @21
    @11
    @20
    @2
    cO
    cO
    cdm
    #
    cN
    cfv
    #
    ccom
    #
    cT
    ccnv
    #
    ccom
    #
    wf1o
    #
    @23
    @11
    @24
    @24
    cxp
    #
    @2
    @26
    wf1o
    #
    @20
    @30
    @27
    wf1o
    #
    @29
    @11
    @24
    @2
    cO
    wf1o
    #
    @30
    @24
    @25
    wf1o
    #
    @31
    @11
    @24
    @2
    cep
    vr
    cv
    #
    cO
    wiso
    #
    @33
    @11
    @2
    cvv
    wcel
    #
    @2
    @35
    wwe
    #
    @36
    vt
    vex
    #
    wps
    wph
    @2
    cA
    wss
    #
    @35
    @20
    wss
    #
    @38
    w3a
    #
    com
    @2
    cdom
    wbr
    #
    wa
    #
    @38
    pwfseqlem5.ps
    @40
    @41
    @38
    @43
    wph
    simprl3
    sylan2b
    #
    @2
    @35
    cO
    cvv
    pwfseqlem5.o
    oiiso
    sylancr
    @24
    @2
    cep
    @35
    cO
    isof1o
    syl
    #
    @11
    @24
    cA
    cpw
    #
    char
    cfv
    #
    wcel
    #
    com
    vb
    cv
    #
    wss
    #
    @50
    @50
    cxp
    #
    @50
    @50
    cN
    cfv
    #
    wf1o
    #
    wi
    #
    vb
    @48
    wral
    #
    com
    @24
    wss
    #
    @34
    @11
    @24
    con0
    wcel
    #
    @24
    @47
    cdom
    wbr
    #
    @49
    @58
    @11
    @37
    @58
    @39
    @2
    @35
    cO
    cvv
    pwfseqlem5.o
    oion
    ax-mp
    #
    a1i
    #
    @11
    @24
    @2
    cen
    wbr
    #
    @2
    @47
    cdom
    wbr
    #
    @59
    @11
    @37
    @38
    @62
    @39
    @45
    @2
    @35
    cO
    cvv
    pwfseqlem5.o
    oien
    sylancr
    #
    @11
    @2
    cA
    cdom
    wbr
    #
    cA
    @47
    cdom
    wbr
    #
    @63
    @11
    cA
    cvv
    wcel
    #
    @40
    @65
    @11
    @47
    cvv
    wcel
    #
    @67
    @11
    @47
    vn
    com
    cA
    @12
    cmap
    co
    #
    ciun
    #
    cG
    wf1
    #
    @70
    cvv
    wcel
    @68
    wph
    @71
    wps
    pwfseqlem5.g
    adantr
    vn
    com
    @69
    omex
    cA
    @12
    cmap
    ovex
    iunex
    @47
    @70
    cvv
    cG
    f1dmex
    sylancl
    cA
    pwexb
    sylibr
    #
    wps
    wph
    @44
    @40
    pwfseqlem5.ps
    @40
    @41
    @38
    @43
    wph
    simprl1
    sylan2b
    @2
    cA
    cvv
    ssdomg
    sylc
    @11
    @67
    cA
    @47
    csdm
    wbr
    @66
    @72
    cA
    cvv
    canth2g
    cA
    @47
    sdomdom
    3syl
    @2
    cA
    @47
    domtr
    syl2anc
    @24
    @2
    @47
    endomtr
    syl2anc
    @47
    @24
    elharval
    sylanbrc
    wph
    @56
    wps
    pwfseqlem5.n
    adantr
    @11
    com
    @24
    ccrd
    cfv
    #
    @24
    @11
    com
    com
    ccrd
    cfv
    #
    @73
    cardom
    @11
    @74
    @73
    wss
    #
    com
    @24
    cdom
    wbr
    #
    @11
    @43
    @2
    @24
    cen
    wbr
    @76
    wps
    wph
    @44
    @43
    pwfseqlem5.ps
    wph
    @42
    @43
    simprr
    sylan2b
    @11
    @24
    @2
    @64
    ensymd
    com
    @2
    @24
    domentr
    syl2anc
    @11
    com
    ccrd
    cdm
    #
    wcel
    #
    @24
    @77
    wcel
    #
    @75
    @76
    wb
    com
    con0
    wcel
    @78
    omelon
    com
    onenon
    ax-mp
    @58
    @79
    @11
    @60
    @24
    onenon
    mp1i
    com
    @24
    carddom2
    sylancr
    mpbird
    syl5eqssr
    @11
    @58
    @73
    @24
    wss
    @61
    @24
    cardonle
    syl
    sstrd
    #
    @55
    @57
    @34
    wi
    vb
    @24
    @48
    @50
    @24
    wceq
    #
    @51
    @57
    @54
    @34
    @50
    @24
    com
    sseq2
    @81
    @54
    @52
    @50
    @25
    wf1o
    #
    @30
    @50
    @25
    wf1o
    #
    @34
    @81
    @53
    @25
    wceq
    @54
    @82
    wb
    @50
    @24
    cN
    fveq2
    @52
    @50
    @53
    @25
    f1oeq1
    syl
    @81
    @52
    @30
    wceq
    #
    @82
    @83
    wb
    @81
    @84
    @50
    @24
    @50
    @24
    xpeq12
    anidms
    @52
    @30
    @50
    @25
    f1oeq2
    syl
    @50
    @24
    @30
    @25
    f1oeq3
    3bitrd
    imbi12d
    rspcv
    syl3c
    @30
    @24
    @2
    cO
    @25
    f1oco
    syl2anc
    @11
    @30
    @20
    cT
    wf1o
    #
    @32
    @11
    @30
    @20
    vu
    vv
    @24
    @24
    vu
    cv
    cO
    cfv
    #
    vv
    cv
    cO
    cfv
    #
    cop
    cmpt2
    #
    wf1o
    #
    @85
    @11
    vu
    vv
    @24
    @2
    @24
    @2
    @86
    @87
    @11
    @33
    @24
    @2
    vu
    @24
    @86
    cmpt
    #
    wf1o
    #
    @46
    @11
    cO
    @90
    wceq
    @33
    @91
    wb
    @11
    vu
    @24
    @2
    cO
    @11
    @33
    @24
    @2
    cO
    wf
    @46
    @24
    @2
    cO
    f1of
    syl
    #
    feqmptd
    @24
    @2
    cO
    @90
    f1oeq1
    syl
    mpbid
    @11
    @33
    @24
    @2
    vv
    @24
    @87
    cmpt
    #
    wf1o
    #
    @46
    @11
    cO
    @93
    wceq
    @33
    @94
    wb
    @11
    vv
    @24
    @2
    cO
    @92
    feqmptd
    @24
    @2
    cO
    @93
    f1oeq1
    syl
    mpbid
    xpf1o
    cT
    @88
    wceq
    @85
    @89
    wb
    pwfseqlem5.t
    @30
    @20
    cT
    @88
    f1oeq1
    ax-mp
    sylibr
    @30
    @20
    cT
    f1ocnv
    syl
    @20
    @30
    @2
    @26
    @27
    f1oco
    syl2anc
    cP
    @28
    wceq
    @23
    @29
    wb
    pwfseqlem5.p
    @20
    @2
    cP
    @28
    f1oeq1
    ax-mp
    sylibr
    #
    @20
    @2
    cP
    f1of1
    syl
    @11
    @18
    cO
    com
    cres
    #
    crn
    #
    @2
    cxp
    #
    cI
    wf1
    #
    @98
    @20
    wss
    #
    @22
    @11
    @18
    @98
    cI
    wf1o
    #
    @99
    @11
    @18
    @98
    vx
    vy
    com
    @2
    vx
    cv
    cO
    cfv
    #
    vy
    cv
    #
    cop
    cmpt2
    #
    wf1o
    #
    @101
    @11
    vx
    vy
    com
    @97
    @2
    @2
    @102
    @103
    @11
    com
    @97
    @96
    wf1o
    #
    com
    @97
    vx
    com
    @102
    cmpt
    #
    wf1o
    #
    @11
    com
    @2
    @96
    wf1
    #
    @106
    @11
    @24
    @2
    cO
    wf1
    #
    @57
    @109
    @11
    @33
    @110
    @46
    @24
    @2
    cO
    f1of1
    syl
    @80
    @24
    @2
    com
    cO
    f1ssres
    syl2anc
    #
    com
    @2
    @96
    f1f1orn
    syl
    @11
    @96
    @107
    wceq
    @106
    @108
    wb
    @11
    vx
    @24
    @2
    com
    cO
    @92
    @80
    feqresmpt
    com
    @97
    @96
    @107
    f1oeq1
    syl
    mpbid
    vy
    @2
    @103
    cmpt
    #
    cid
    @2
    cres
    #
    wceq
    #
    @2
    @2
    @112
    wf1o
    #
    @11
    vy
    @2
    mptresid
    @114
    @115
    @2
    @2
    @113
    wf1o
    @2
    f1oi
    @2
    @2
    @112
    @113
    f1oeq1
    mpbiri
    mp1i
    xpf1o
    cI
    @104
    wceq
    @101
    @105
    wb
    pwfseqlem5.i
    @18
    @98
    cI
    @104
    f1oeq1
    ax-mp
    sylibr
    @18
    @98
    cI
    f1of1
    syl
    @11
    @109
    com
    @2
    @96
    wf
    @97
    @2
    wss
    @100
    @111
    com
    @2
    @96
    f1f
    com
    @2
    @96
    frn
    @97
    @2
    @2
    xpss1
    4syl
    @18
    @98
    @20
    cI
    f1ss
    syl2anc
    @18
    @20
    @2
    cP
    cI
    f1co
    syl2anc
    @11
    vx
    vy
    @2
    c0
    cO
    cfv
    vf
    vn
    vk
    cP
    cS
    cQ
    cvv
    @37
    @11
    @39
    a1i
    @11
    @24
    @2
    c0
    cO
    @92
    @11
    com
    @24
    c0
    @80
    c0
    com
    wcel
    @11
    peano1
    a1i
    sseldd
    ffvelrnd
    @95
    pwfseqlem5.s
    pwfseqlem5.q
    fseqenlem2
    @13
    @18
    @2
    @14
    cQ
    f1co
    syl2anc
    cK
    @15
    wceq
    @17
    @16
    wb
    pwfseqlem5.k
    @13
    @2
    cK
    @15
    f1eq1
    ax-mp
    sylibr
    @3
    eqid
    @4
    eqid
    vc
    vm
    vb
    vw
    vj
    cA
    @4
    @9
    vs
    vd
    va
    @9
    eqid
    fpwwe2cbv
    @10
    eqid
    pwfseqlem4
end
