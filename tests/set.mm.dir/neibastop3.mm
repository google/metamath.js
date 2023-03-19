include "cv.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "wi.mm"
include "wal.mm"
include "neibastop1.mm"
include "cab.mm"
include "wss.mm"
include "neibastop2.mm"
include "selpw.mm"
include "anbi1i.mm"
include "syl6bbr.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "ralrimiva.mm"
include "sneq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "neeq1d.mm"
include "rabbidv.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "cuni.mm"
include "toponuni.mm"
include "eqimss2.mm"
include "syl.mm"
include "sspwuni.mm"
include "ad2antlr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wrex.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "ad3antlr.mm"
include "eltop2.mm"
include "elpwi.mm"
include "ssralv.mm"
include "adantl.mm"
include "simprr.mm"
include "eleq2d.mm"
include "sseq2d.mm"
include "biimpa.mm"
include "sylan2.mm"
include "sselda.mm"
include "adantrr.mm"
include "adantr.mm"
include "eqid.mm"
include "isneip.mm"
include "baibd.mm"
include "syl21anc.mm"
include "pweq.mm"
include "ineq2d.mm"
include "elrab3.mm"
include "3bitr3d.mm"
include "expr.mm"
include "ralimdva.mm"
include "syld.mm"
include "imp.mm"
include "an32s.mm"
include "ralbi.mm"
include "bitrd.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"
include "expl.mm"
include "alrimiv.mm"
include "eleq1.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "eqeu.mm"
include "syl121anc.mm"
include "df-reu.mm"

theorem neibastop3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let vj: setvar j
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  let vz: setvar z
  let cG: class G
  let vs: setvar s
  let vu: setvar u
  let cP: class P
  let cN: class N
  let cS: class S
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume neibastop1.1: |- ( ph -> X e. V )
  assume neibastop1.2: |- ( ph -> F : X --> ( ~P ~P X \ { (/) } ) )
  assume neibastop1.3: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) /\ w e. ( F ` x ) ) ) -> ( ( F ` x ) i^i ~P ( v i^i w ) ) =/= (/) )
  assume neibastop1.4: |- J = { o e. ~P X | A. x e. o ( ( F ` x ) i^i ~P o ) =/= (/) }
  assume neibastop1.5: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> x e. v )
  assume neibastop1.6: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> E. t e. ( F ` x ) A. y e. t ( ( F ` y ) i^i ~P v ) =/= (/) )

  disjoint n t
  disjoint n v
  disjoint n y
  disjoint t v
  disjoint t y
  disjoint v y
  disjoint j n
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n x
  disjoint J n
  disjoint v x
  disjoint J v
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint o t
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint t w
  disjoint t x
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint j o
  disjoint j t
  disjoint j w
  disjoint F j
  disjoint n o
  disjoint n w
  disjoint F n
  disjoint F o
  disjoint F t
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint j ph
  disjoint n ph
  disjoint o ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint X j
  disjoint X n
  disjoint X o
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f v
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint k n
  disjoint k t
  disjoint k v
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n z
  disjoint G n
  disjoint t z
  disjoint G t
  disjoint v z
  disjoint G v
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint j s
  disjoint j u
  disjoint j z
  disjoint n s
  disjoint n u
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint x z
  disjoint J z
  disjoint f o
  disjoint f s
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint P f
  disjoint o s
  disjoint o u
  disjoint o z
  disjoint P o
  disjoint s t
  disjoint s w
  disjoint P s
  disjoint t u
  disjoint P t
  disjoint u w
  disjoint P u
  disjoint P v
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint N f
  disjoint k o
  disjoint k s
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint N k
  disjoint N o
  disjoint N s
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint S f
  disjoint S k
  disjoint S o
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint U f
  disjoint U k
  disjoint U n
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a o
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b f
  disjoint b g
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b o
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint f g
  disjoint f j
  disjoint F f
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g o
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F z
  disjoint f ph
  disjoint k ph
  disjoint ph s
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X s
  disjoint X u
  disjoint X z
  assert |- ( ph -> E! j e. ( TopOn ` X ) A. x e. X ( ( nei ` j ) ` { x } ) = { n e. ~P X | ( ( F ` x ) i^i ~P n ) =/= (/) } )

  proof
    wph
    vj
    cv
    #
    cX
    ctopon
    cfv
    #
    wcel
    #
    vx
    cv
    #
    csn
    #
    @0
    cnei
    cfv
    #
    cfv
    #
    @3
    cF
    cfv
    #
    vn
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vn
    cX
    cpw
    #
    crab
    #
    wceq
    #
    vx
    cX
    wral
    #
    wa
    #
    vj
    weu
    #
    @15
    vj
    @1
    wreu
    wph
    cJ
    @1
    wcel
    #
    @18
    @4
    cJ
    cnei
    cfv
    #
    cfv
    #
    @13
    wceq
    #
    vx
    cX
    wral
    #
    @16
    @0
    cJ
    wceq
    #
    wi
    #
    vj
    wal
    @17
    wph
    vx
    vw
    vv
    vo
    cF
    cJ
    cV
    cX
    neibastop1.1
    neibastop1.2
    neibastop1.3
    neibastop1.4
    neibastop1
    #
    @25
    wph
    vz
    cv
    #
    csn
    #
    @19
    cfv
    #
    @26
    cF
    cfv
    #
    @9
    cin
    #
    c0
    wne
    #
    vn
    @12
    crab
    #
    wceq
    #
    vz
    cX
    wral
    @22
    wph
    @33
    vz
    cX
    wph
    @26
    cX
    wcel
    wa
    #
    @28
    @8
    @12
    wcel
    #
    @31
    wa
    #
    vn
    cab
    @32
    @34
    @36
    vn
    @28
    @34
    @8
    @28
    wcel
    @8
    cX
    wss
    #
    @31
    wa
    @36
    wph
    vx
    vy
    vw
    vv
    vt
    @26
    vo
    cF
    cJ
    @8
    cV
    cX
    neibastop1.1
    neibastop1.2
    neibastop1.3
    neibastop1.4
    neibastop1.5
    neibastop1.6
    neibastop2
    @35
    @37
    @31
    vn
    cX
    selpw
    anbi1i
    syl6bbr
    abbi2dv
    @31
    vn
    @12
    df-rab
    syl6eqr
    ralrimiva
    @21
    @33
    vx
    vz
    cX
    @3
    @26
    wceq
    #
    @20
    @28
    @13
    @32
    @38
    @4
    @27
    @19
    @3
    @26
    sneq
    fveq2d
    @38
    @11
    @31
    vn
    @12
    @38
    @10
    @30
    c0
    @38
    @7
    @29
    @9
    @3
    @26
    cF
    fveq2
    ineq1d
    neeq1d
    rabbidv
    eqeq12d
    cbvralv
    sylibr
    wph
    @24
    vj
    wph
    @2
    @15
    @23
    wph
    @2
    wa
    #
    @15
    wa
    #
    @12
    @0
    cin
    #
    @0
    cJ
    @40
    @0
    @12
    wss
    #
    @41
    @0
    wceq
    @2
    @42
    wph
    @15
    @2
    @0
    cuni
    #
    cX
    wss
    #
    @42
    @2
    cX
    @43
    wceq
    #
    @44
    cX
    @0
    toponuni
    #
    @43
    cX
    eqimss2
    syl
    @0
    cX
    sspwuni
    sylibr
    ad2antlr
    @0
    @12
    sseqin2
    sylib
    @40
    @41
    @7
    vo
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @47
    wral
    #
    vo
    @12
    crab
    cJ
    @40
    @51
    vo
    @12
    @0
    @40
    @47
    @12
    wcel
    #
    wa
    #
    @47
    @0
    wcel
    #
    @3
    @26
    wcel
    @26
    @47
    wss
    wa
    vz
    @0
    wrex
    #
    vx
    @47
    wral
    #
    @51
    @53
    @0
    ctop
    wcel
    #
    @54
    @56
    wb
    @2
    @57
    wph
    @15
    @52
    cX
    @0
    topontop
    #
    ad3antlr
    vx
    vz
    @47
    @0
    eltop2
    syl
    @53
    @55
    @50
    wb
    #
    vx
    @47
    wral
    #
    @56
    @51
    wb
    @39
    @52
    @15
    @60
    @39
    @52
    wa
    #
    @15
    @60
    @61
    @15
    @14
    vx
    @47
    wral
    #
    @60
    @52
    @15
    @62
    wi
    #
    @39
    @52
    @47
    cX
    wss
    #
    @63
    @47
    cX
    elpwi
    #
    @14
    vx
    @47
    cX
    ssralv
    syl
    adantl
    @61
    @14
    @59
    vx
    @47
    @61
    @3
    @47
    wcel
    #
    @14
    @59
    @61
    @66
    @14
    wa
    #
    wa
    #
    @47
    @6
    wcel
    #
    @47
    @13
    wcel
    #
    @55
    @50
    @68
    @6
    @13
    @47
    @61
    @66
    @14
    simprr
    eleq2d
    @68
    @57
    @3
    @43
    wcel
    #
    @47
    @43
    wss
    #
    @69
    @55
    wb
    @2
    @57
    wph
    @52
    @67
    @58
    ad3antlr
    @61
    @66
    @71
    @14
    @61
    @47
    @43
    @3
    @52
    @39
    @64
    @72
    @65
    @39
    @64
    @72
    @39
    cX
    @43
    @47
    @2
    @45
    wph
    @46
    adantl
    sseq2d
    biimpa
    sylan2
    #
    sselda
    adantrr
    @61
    @72
    @67
    @73
    adantr
    @57
    @71
    wa
    @69
    @72
    @55
    @3
    vz
    @0
    @47
    @43
    @43
    eqid
    isneip
    baibd
    syl21anc
    @52
    @70
    @50
    wb
    @39
    @67
    @11
    @50
    vn
    @47
    @12
    @8
    @47
    wceq
    #
    @10
    @49
    c0
    @74
    @9
    @48
    @7
    @8
    @47
    pweq
    ineq2d
    neeq1d
    elrab3
    ad2antlr
    3bitr3d
    expr
    ralimdva
    syld
    imp
    an32s
    @55
    @50
    vx
    @47
    ralbi
    syl
    bitrd
    rabbi2dva
    neibastop1.4
    syl6eqr
    eqtr3d
    expl
    alrimiv
    @16
    @18
    @22
    wa
    vj
    cJ
    @1
    @23
    @2
    @18
    @15
    @22
    @0
    cJ
    @1
    eleq1
    @23
    @14
    @21
    vx
    cX
    @23
    @6
    @20
    @13
    @23
    @4
    @5
    @19
    @0
    cJ
    cnei
    fveq2
    fveq1d
    eqeq1d
    ralbidv
    anbi12d
    eqeu
    syl121anc
    @15
    vj
    @1
    df-reu
    sylibr
end
