include "cdm.mm"
include "wfo.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "efgsf.mm"
include "fdmi.mm"
include "feq2i.mm"
include "mpbir.mm"
include "wss.mm"
include "frn.mm"
include "ax-mp.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "c2o.mm"
include "cxp.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "lencl.mm"
include "syl.mm"
include "peano2nn0.mm"
include "wn.mm"
include "nn0nlt0.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "sseq1d.mm"
include "weq.mm"
include "rabbidv.mm"
include "0ss.mm"
include "cun.mm"
include "simpr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "w3a.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "rneqd.mm"
include "eleq2d.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "simpl1r.mm"
include "simprl.mm"
include "c2.mm"
include "cr.mm"
include "crp.mm"
include "sseldi.mm"
include "nn0red.mm"
include "2rp.mm"
include "ltaddrp.mm"
include "sylancl.mm"
include "efgtlen.mm"
include "adantl.mm"
include "simpl3.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "sseldd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "sylib.mm"
include "cs1.mm"
include "cconcat.mm"
include "simprrl.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "eldifi.mm"
include "3syl.mm"
include "simpl2.mm"
include "simprlr.mm"
include "simprrr.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "efgsp1.mm"
include "syl2anc.mm"
include "efgsval2.mm"
include "syl3anc.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "anassrs.mm"
include "rexlimddv.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "wi.mm"
include "eldif.mm"
include "eleq2i.mm"
include "efgs1.mm"
include "sylbir.mm"
include "efgsval.mm"
include "s1len.mm"
include "oveq1i.mm"
include "1m1e0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "s1fv.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "pm2.61d.mm"
include "rabssdv.mm"
include "syl5eqss.mm"
include "unssd.mm"
include "wo.mm"
include "cle.mm"
include "id.mm"
include "nn0leltp1.mm"
include "syl2anr.mm"
include "nn0re.mm"
include "leloe.mm"
include "bitr3d.mm"
include "rabbidva.mm"
include "unrab.mm"
include "syl6eqr.mm"
include "sylibrd.mm"
include "nn0ind.mm"
include "ltp1d.mm"
include "ssriv.mm"
include "eqssi.mm"
include "dffo2.mm"
include "mpbir2an.mm"

theorem efgsfo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cD: class D
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cI: class I
  let cM: class M
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let cA: class A
  let cJ: class J
  let cL: class L
  let cF: class F
  let cK: class K
  let cP: class P
  let wph: wff ph
  let cN: class N
  let cU: class U
  let vo: setvar o
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cB: class B
  let cC: class C
  let cY: class Y
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )
  assume efgval2.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume efgval2.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume efgred.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume efgred.s: |- S = ( m e. { t e. ( Word W \ { (/) } ) | ( ( t ` 0 ) e. D /\ A. k e. ( 1 ..^ ( # ` t ) ) ( t ` k ) e. ran ( T ` ( t ` ( k - 1 ) ) ) ) } |-> ( m ` ( ( # ` m ) - 1 ) ) )

  disjoint y z
  disjoint n t
  disjoint n v
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint m n
  disjoint m t
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint M m
  disjoint n x
  disjoint M n
  disjoint t x
  disjoint M t
  disjoint v x
  disjoint M v
  disjoint w x
  disjoint M w
  disjoint M x
  disjoint k m
  disjoint k t
  disjoint k x
  disjoint T k
  disjoint T m
  disjoint T t
  disjoint T x
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint W k
  disjoint m y
  disjoint m z
  disjoint W m
  disjoint W n
  disjoint W t
  disjoint W v
  disjoint W w
  disjoint x y
  disjoint x z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint D m
  disjoint D t
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a j
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint b j
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint A b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c r
  disjoint c s
  disjoint c u
  disjoint A c
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d j
  disjoint d r
  disjoint d s
  disjoint d u
  disjoint A d
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint A f
  disjoint g h
  disjoint g i
  disjoint g j
  disjoint g r
  disjoint g s
  disjoint g u
  disjoint A g
  disjoint h i
  disjoint h j
  disjoint h r
  disjoint h s
  disjoint h u
  disjoint A h
  disjoint i j
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint A i
  disjoint j r
  disjoint j s
  disjoint j u
  disjoint A j
  disjoint r s
  disjoint r u
  disjoint A r
  disjoint s u
  disjoint A s
  disjoint A u
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint J y
  disjoint J z
  disjoint L a
  disjoint L b
  disjoint L f
  disjoint L g
  disjoint L h
  disjoint L r
  disjoint L s
  disjoint L u
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F i
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K r
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint P c
  disjoint P n
  disjoint P t
  disjoint P v
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint c ph
  disjoint i ph
  disjoint j ph
  disjoint ph r
  disjoint ph s
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint M a
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint M b
  disjoint c m
  disjoint c x
  disjoint M c
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint M f
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint M g
  disjoint i m
  disjoint i n
  disjoint i t
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint M i
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint M j
  disjoint m r
  disjoint m s
  disjoint m u
  disjoint n r
  disjoint n s
  disjoint n u
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint M r
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint M s
  disjoint t u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint M u
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N r
  disjoint U n
  disjoint U v
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint a k
  disjoint a o
  disjoint T a
  disjoint b k
  disjoint b o
  disjoint T b
  disjoint c k
  disjoint c o
  disjoint T c
  disjoint f k
  disjoint f o
  disjoint T f
  disjoint g k
  disjoint g o
  disjoint T g
  disjoint i k
  disjoint i o
  disjoint T i
  disjoint j k
  disjoint j o
  disjoint T j
  disjoint k o
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint m o
  disjoint o r
  disjoint o s
  disjoint o t
  disjoint o u
  disjoint o x
  disjoint T o
  disjoint T r
  disjoint T s
  disjoint T u
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint X u
  disjoint Q c
  disjoint Q n
  disjoint Q t
  disjoint Q v
  disjoint Q w
  disjoint Q y
  disjoint Q z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d t
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint W d
  disjoint f y
  disjoint f z
  disjoint W f
  disjoint g y
  disjoint g z
  disjoint W g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h o
  disjoint h t
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint W h
  disjoint i y
  disjoint i z
  disjoint W i
  disjoint j y
  disjoint j z
  disjoint W j
  disjoint n o
  disjoint o v
  disjoint o w
  disjoint o y
  disjoint o z
  disjoint W o
  disjoint W r
  disjoint s y
  disjoint s z
  disjoint W s
  disjoint u y
  disjoint u z
  disjoint W u
  disjoint .~ a
  disjoint .~ b
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ i
  disjoint .~ j
  disjoint .~ r
  disjoint .~ s
  disjoint .~ u
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B i
  disjoint B j
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint C a
  disjoint C b
  disjoint C i
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint S o
  disjoint S r
  disjoint S s
  disjoint S u
  disjoint Y i
  disjoint Y j
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I f
  disjoint I g
  disjoint I i
  disjoint I j
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- S : dom S -onto-> W

  proof
    cS
    cdm
    #
    cW
    cS
    wfo
    @0
    cW
    cS
    wf
    #
    cS
    crn
    #
    cW
    wceq
    @1
    cc0
    vt
    cv
    #
    cfv
    cD
    wcel
    vk
    cv
    #
    @3
    cfv
    @4
    c1
    cmin
    co
    @3
    cfv
    cT
    cfv
    crn
    wcel
    vk
    c1
    @3
    chash
    cfv
    cfzo
    co
    wral
    wa
    vt
    cW
    cword
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    cW
    cS
    wf
    vx
    vy
    vz
    vw
    vv
    vt
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsf
    #
    @0
    @8
    cW
    cS
    @8
    cW
    cS
    @9
    fdmi
    feq2i
    mpbir
    #
    @2
    cW
    @1
    @2
    cW
    wss
    @10
    @0
    cW
    cS
    frn
    ax-mp
    vc
    cW
    @2
    vc
    cv
    #
    cW
    wcel
    #
    va
    cv
    #
    chash
    cfv
    #
    @11
    chash
    cfv
    #
    c1
    caddc
    co
    #
    clt
    wbr
    #
    va
    cW
    crab
    #
    @2
    @11
    @12
    @15
    cn0
    wcel
    #
    @16
    cn0
    wcel
    @18
    @2
    wss
    #
    @12
    @11
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    @19
    cW
    @22
    @11
    cW
    @22
    cid
    cfv
    @22
    efgval.w
    @22
    fviss
    eqsstri
    #
    sseli
    @21
    @11
    lencl
    syl
    #
    @15
    peano2nn0
    @14
    vb
    cv
    #
    clt
    wbr
    #
    va
    cW
    crab
    #
    @2
    wss
    c0
    @2
    wss
    @14
    vd
    cv
    #
    clt
    wbr
    #
    va
    cW
    crab
    #
    @2
    wss
    #
    @14
    @28
    c1
    caddc
    co
    #
    clt
    wbr
    #
    va
    cW
    crab
    #
    @2
    wss
    #
    @20
    vb
    vd
    @16
    @25
    cc0
    wceq
    #
    @27
    c0
    @2
    @36
    @26
    wn
    #
    va
    cW
    wral
    @27
    c0
    wceq
    @36
    @37
    va
    cW
    @13
    cW
    wcel
    #
    @14
    cn0
    wcel
    #
    @36
    @37
    @38
    @13
    @22
    wcel
    @39
    cW
    @22
    @13
    @23
    sseli
    @21
    @13
    lencl
    syl
    #
    @39
    @37
    @36
    @14
    cc0
    clt
    wbr
    #
    wn
    @14
    nn0nlt0
    @36
    @26
    @41
    @25
    cc0
    @14
    clt
    breq2
    notbid
    syl5ibr
    syl5
    ralrimiv
    @26
    va
    cW
    rabeq0
    sylibr
    sseq1d
    vb
    vd
    weq
    #
    @27
    @30
    @2
    @42
    @26
    @29
    va
    cW
    @25
    @28
    @14
    clt
    breq2
    rabbidv
    sseq1d
    @25
    @32
    wceq
    #
    @27
    @34
    @2
    @43
    @26
    @33
    va
    cW
    @25
    @32
    @14
    clt
    breq2
    rabbidv
    sseq1d
    @25
    @16
    wceq
    #
    @27
    @18
    @2
    @44
    @26
    @17
    va
    cW
    @25
    @16
    @14
    clt
    breq2
    rabbidv
    sseq1d
    @2
    0ss
    @28
    cn0
    wcel
    #
    @31
    @30
    @14
    @28
    wceq
    #
    va
    cW
    crab
    #
    cun
    #
    @2
    wss
    #
    @35
    @45
    @31
    @49
    @45
    @31
    wa
    #
    @30
    @47
    @2
    @45
    @31
    simpr
    @50
    @47
    @15
    @28
    wceq
    #
    vc
    cW
    crab
    @2
    @46
    @51
    va
    vc
    cW
    va
    vc
    weq
    #
    @14
    @15
    @28
    @13
    @11
    chash
    fveq2
    #
    eqeq1d
    cbvrabv
    @50
    @51
    vc
    cW
    @2
    @50
    @12
    @51
    w3a
    #
    @11
    vx
    cW
    vx
    cv
    #
    cT
    cfv
    #
    crn
    #
    ciun
    #
    wcel
    #
    @11
    @2
    wcel
    #
    @59
    @11
    @25
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vb
    cW
    wrex
    #
    @54
    @60
    @59
    @11
    @57
    wcel
    #
    vx
    cW
    wrex
    @64
    vx
    @11
    cW
    @57
    eliun
    @65
    @63
    vx
    vb
    cW
    vx
    vb
    weq
    #
    @57
    @62
    @11
    @66
    @56
    @61
    @55
    @25
    cT
    fveq2
    rneqd
    eleq2d
    cbvrexv
    bitri
    @54
    @63
    @60
    vb
    cW
    @54
    @25
    cW
    wcel
    #
    @63
    wa
    #
    wa
    #
    vo
    cv
    #
    cS
    cfv
    #
    @25
    wceq
    #
    @60
    vo
    @0
    @69
    @25
    @2
    wcel
    #
    @72
    vo
    @0
    wrex
    #
    @69
    @30
    @2
    @25
    @45
    @31
    @12
    @51
    @68
    simpl1r
    @69
    @67
    @25
    chash
    cfv
    #
    @28
    clt
    wbr
    #
    @25
    @30
    wcel
    @54
    @67
    @63
    simprl
    #
    @69
    @75
    @75
    c2
    caddc
    co
    #
    @28
    clt
    @69
    @75
    cr
    wcel
    c2
    crp
    wcel
    @75
    @78
    clt
    wbr
    @69
    @75
    @69
    @25
    @22
    wcel
    @75
    cn0
    wcel
    @69
    cW
    @22
    @25
    @23
    @77
    sseldi
    @21
    @25
    lencl
    syl
    nn0red
    2rp
    @75
    c2
    ltaddrp
    sylancl
    @69
    @15
    @78
    @28
    @68
    @15
    @78
    wceq
    @54
    vy
    vz
    vw
    vv
    @11
    c.sm
    cT
    vn
    cI
    cM
    cW
    @25
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtlen
    adantl
    @50
    @12
    @51
    @68
    simpl3
    eqtr3d
    breqtrd
    @29
    @76
    va
    @25
    cW
    va
    vb
    weq
    @14
    @75
    @28
    clt
    @13
    @25
    chash
    fveq2
    breq1d
    elrab
    sylanbrc
    sseldd
    cS
    @0
    wfn
    #
    @73
    @74
    wb
    @1
    @79
    @10
    @0
    cW
    cS
    ffn
    ax-mp
    #
    vo
    @0
    @25
    cS
    fvelrnb
    ax-mp
    sylib
    @54
    @68
    @70
    @0
    wcel
    #
    @72
    wa
    #
    @60
    @54
    @68
    @82
    wa
    #
    wa
    #
    @70
    @11
    cs1
    #
    cconcat
    co
    #
    cS
    cfv
    #
    @11
    @2
    @84
    @70
    @5
    wcel
    #
    @12
    @86
    @0
    wcel
    #
    @87
    @11
    wceq
    @84
    @81
    @70
    @7
    wcel
    #
    @88
    @54
    @68
    @81
    @72
    simprrl
    #
    @81
    @90
    cc0
    @70
    cfv
    cD
    wcel
    vi
    cv
    #
    @70
    cfv
    @92
    c1
    cmin
    co
    @70
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @70
    chash
    cfv
    cfzo
    co
    wral
    vx
    vy
    vz
    vw
    vv
    vt
    cD
    c.sm
    cS
    cT
    vi
    vk
    vm
    vn
    @70
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsdm
    simp1bi
    @70
    @5
    @6
    eldifi
    3syl
    @50
    @12
    @51
    @83
    simpl2
    @84
    @81
    @11
    @71
    cT
    cfv
    #
    crn
    #
    wcel
    @89
    @91
    @84
    @11
    @62
    @94
    @54
    @67
    @63
    @82
    simprlr
    @84
    @93
    @61
    @84
    @71
    @25
    cT
    @54
    @68
    @81
    @72
    simprrr
    fveq2d
    rneqd
    eleqtrrd
    vx
    vy
    vz
    vw
    vv
    vt
    @11
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    @70
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsp1
    syl2anc
    #
    vx
    vy
    vz
    vw
    vv
    vt
    @70
    @11
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsval2
    syl3anc
    @84
    @79
    @89
    @87
    @2
    wcel
    @80
    @95
    @0
    @86
    cS
    fnfvelrn
    sylancr
    eqeltrrd
    anassrs
    rexlimddv
    rexlimdvaa
    syl5bi
    @12
    @50
    @59
    wn
    #
    @60
    wi
    @51
    @12
    @96
    @60
    @12
    @96
    wa
    #
    @85
    cS
    cfv
    #
    @11
    @2
    @97
    @98
    @85
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @85
    cfv
    #
    cc0
    @85
    cfv
    #
    @11
    @97
    @85
    @0
    wcel
    #
    @98
    @101
    wceq
    @97
    @11
    cW
    @58
    cdif
    #
    wcel
    #
    @103
    @11
    cW
    @58
    eldif
    @105
    @11
    cD
    wcel
    @103
    cD
    @104
    @11
    efgred.d
    eleq2i
    vx
    vy
    vz
    vw
    vv
    vt
    @11
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgs1
    sylbir
    sylbir
    #
    vx
    vy
    vz
    vw
    vv
    vt
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    @85
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsval
    syl
    @101
    @102
    wceq
    @97
    @100
    cc0
    @85
    @100
    c1
    c1
    cmin
    co
    cc0
    @99
    c1
    c1
    cmin
    @11
    s1len
    oveq1i
    1m1e0
    eqtri
    fveq2i
    a1i
    @12
    @102
    @11
    wceq
    @96
    @11
    cW
    s1fv
    adantr
    3eqtrd
    @97
    @79
    @103
    @98
    @2
    wcel
    @80
    @106
    @0
    @85
    cS
    fnfvelrn
    sylancr
    eqeltrrd
    ex
    3ad2ant2
    pm2.61d
    rabssdv
    syl5eqss
    unssd
    ex
    @45
    @34
    @48
    @2
    @45
    @34
    @29
    @46
    wo
    #
    va
    cW
    crab
    @48
    @45
    @33
    @107
    va
    cW
    @45
    @38
    wa
    @14
    @28
    cle
    wbr
    #
    @33
    @107
    @38
    @39
    @45
    @108
    @33
    wb
    @45
    @40
    @45
    id
    @14
    @28
    nn0leltp1
    syl2anr
    @38
    @14
    cr
    wcel
    @28
    cr
    wcel
    @108
    @107
    wb
    @45
    @38
    @14
    @40
    nn0red
    @28
    nn0re
    @14
    @28
    leloe
    syl2anr
    bitr3d
    rabbidva
    @29
    @46
    va
    cW
    unrab
    syl6eqr
    sseq1d
    sylibrd
    nn0ind
    3syl
    @12
    @12
    @15
    @16
    clt
    wbr
    #
    @11
    @18
    wcel
    @12
    id
    @12
    @15
    @12
    @15
    @24
    nn0red
    ltp1d
    @17
    @109
    va
    @11
    cW
    @52
    @14
    @15
    @16
    clt
    @53
    breq1d
    elrab
    sylanbrc
    sseldd
    ssriv
    eqssi
    @0
    cW
    cS
    dffo2
    mpbir2an
end
