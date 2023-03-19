include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cn0.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "wf.mm"
include "cmin.mm"
include "crn.mm"
include "cfzo.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "efgsf.mm"
include "fdmi.mm"
include "feq2i.mm"
include "mpbir.mm"
include "ffvelrni.mm"
include "adantr.mm"
include "sseldi.mm"
include "lencl.mm"
include "syl.mm"
include "peano2nn0.mm"
include "breq2.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "weq.mm"
include "wn.mm"
include "nn0nlt0.mm"
include "pm2.21d.mm"
include "rgen2a.mm"
include "w3a.mm"
include "simpl1.mm"
include "wb.mm"
include "simpl3l.mm"
include "mpbird.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3r.mm"
include "simpr.mm"
include "efgredlem.mm"
include "iman.mm"
include "3expia.mm"
include "expd.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "cbvral2v.mm"
include "sylib.mm"
include "ancli.mm"
include "wo.mm"
include "cle.mm"
include "nn0leltp1.mm"
include "cr.mm"
include "nn0re.mm"
include "leloe.mm"
include "syl2an.mm"
include "bitr3d.mm"
include "ancoms.mm"
include "sylan2.mm"
include "jaob.mm"
include "syl6bb.mm"
include "2ralbidva.mm"
include "r19.26-2.mm"
include "syl5ibr.mm"
include "nn0ind.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "breq1d.mm"
include "rspc2v.mm"
include "mp2d.mm"
include "3impia.mm"

theorem efgred
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
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
  assert |- ( ( A e. dom S /\ B e. dom S /\ ( S ` A ) = ( S ` B ) ) -> ( A ` 0 ) = ( B ` 0 ) )

  proof
    cA
    cS
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    wceq
    #
    cc0
    cA
    cfv
    #
    cc0
    cB
    cfv
    #
    wceq
    #
    @1
    @2
    wa
    #
    va
    cv
    #
    cS
    cfv
    #
    chash
    cfv
    #
    @3
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
    @11
    vb
    cv
    #
    cS
    cfv
    #
    wceq
    #
    cc0
    @10
    cfv
    #
    cc0
    @16
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    #
    @13
    @14
    clt
    wbr
    #
    @5
    @8
    wi
    #
    @9
    @14
    cn0
    wcel
    #
    @24
    @9
    @13
    cn0
    wcel
    #
    @27
    @9
    @3
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    @28
    @9
    cW
    @30
    @3
    cW
    @30
    cid
    cfv
    @30
    efgval.w
    @30
    fviss
    eqsstri
    #
    @1
    @3
    cW
    wcel
    @2
    @0
    cW
    cA
    cS
    @0
    cW
    cS
    wf
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
    @32
    cfv
    @33
    c1
    cmin
    co
    @32
    cfv
    cT
    cfv
    crn
    wcel
    vk
    c1
    @32
    chash
    cfv
    cfzo
    co
    wral
    wa
    vt
    cW
    cword
    c0
    csn
    cdif
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
    @34
    cW
    cS
    @34
    cW
    cS
    @35
    fdmi
    feq2i
    mpbir
    #
    ffvelrni
    adantr
    sseldi
    @29
    @3
    lencl
    syl
    #
    @13
    peano2nn0
    syl
    @12
    vc
    cv
    #
    clt
    wbr
    #
    @22
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    @12
    cc0
    clt
    wbr
    #
    @22
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    @12
    vi
    cv
    #
    clt
    wbr
    #
    @22
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    #
    @12
    @43
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @22
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    #
    @24
    vc
    vi
    @14
    @38
    cc0
    wceq
    #
    @40
    @42
    va
    vb
    @0
    @0
    @51
    @39
    @41
    @22
    @38
    cc0
    @12
    clt
    breq2
    imbi1d
    2ralbidv
    vc
    vi
    weq
    #
    @40
    @45
    va
    vb
    @0
    @0
    @52
    @39
    @44
    @22
    @38
    @43
    @12
    clt
    breq2
    imbi1d
    2ralbidv
    @38
    @47
    wceq
    #
    @40
    @49
    va
    vb
    @0
    @0
    @53
    @39
    @48
    @22
    @38
    @47
    @12
    clt
    breq2
    imbi1d
    2ralbidv
    @38
    @14
    wceq
    #
    @40
    @23
    va
    vb
    @0
    @0
    @54
    @39
    @15
    @22
    @38
    @14
    @12
    clt
    breq2
    imbi1d
    2ralbidv
    @42
    va
    vb
    @0
    @10
    @0
    wcel
    #
    @42
    @16
    @0
    wcel
    #
    @55
    @41
    @22
    @55
    @12
    cn0
    wcel
    #
    @41
    wn
    @55
    @11
    @30
    wcel
    @57
    @55
    cW
    @30
    @11
    @31
    @0
    cW
    @10
    cS
    @36
    ffvelrni
    sseldi
    @29
    @11
    lencl
    syl
    #
    @12
    nn0nlt0
    syl
    pm2.21d
    adantr
    rgen2a
    @46
    @50
    @43
    cn0
    wcel
    #
    @46
    @12
    @43
    wceq
    #
    @22
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    #
    wa
    #
    @46
    @62
    @46
    @38
    cS
    cfv
    #
    chash
    cfv
    #
    @43
    wceq
    #
    @64
    vd
    cv
    #
    cS
    cfv
    #
    wceq
    #
    cc0
    @38
    cfv
    #
    cc0
    @67
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    vd
    @0
    wral
    vc
    @0
    wral
    @62
    @46
    @74
    vc
    vd
    @0
    @0
    @46
    @38
    @0
    wcel
    #
    @67
    @0
    wcel
    #
    wa
    #
    wa
    @66
    @69
    @72
    @46
    @77
    @66
    @69
    wa
    #
    @72
    @46
    @77
    @78
    w3a
    #
    @72
    wi
    @79
    @72
    wn
    #
    wa
    #
    wn
    @81
    vx
    vy
    vz
    vw
    vv
    vt
    @38
    @67
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
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    @81
    @12
    @65
    clt
    wbr
    #
    @22
    wi
    #
    vb
    @0
    wral
    va
    @0
    wral
    #
    @46
    @46
    @77
    @78
    @80
    simpl1
    @81
    @66
    @84
    @46
    wb
    @66
    @69
    @46
    @77
    @80
    simpl3l
    @66
    @83
    @45
    va
    vb
    @0
    @0
    @66
    @82
    @44
    @22
    @65
    @43
    @12
    clt
    breq2
    imbi1d
    2ralbidv
    syl
    mpbird
    @75
    @76
    @46
    @78
    @80
    simpl2l
    @75
    @76
    @46
    @78
    @80
    simpl2r
    @66
    @69
    @46
    @77
    @80
    simpl3r
    @79
    @80
    simpr
    efgredlem
    @79
    @72
    iman
    mpbir
    3expia
    expd
    ralrimivva
    @74
    @61
    @60
    @11
    @68
    wceq
    #
    @19
    @71
    wceq
    #
    wi
    #
    wi
    vc
    vd
    va
    vb
    @0
    @0
    vc
    va
    weq
    #
    @66
    @60
    @73
    @87
    @88
    @65
    @12
    @43
    @88
    @64
    @11
    chash
    @38
    @10
    cS
    fveq2
    #
    fveq2d
    eqeq1d
    @88
    @69
    @85
    @72
    @86
    @88
    @64
    @11
    @68
    @89
    eqeq1d
    @88
    @70
    @19
    @71
    cc0
    @38
    @10
    fveq1
    eqeq1d
    imbi12d
    imbi12d
    vd
    vb
    weq
    #
    @87
    @22
    @60
    @90
    @85
    @18
    @86
    @21
    @90
    @68
    @17
    @11
    @67
    @16
    cS
    fveq2
    eqeq2d
    @90
    @71
    @20
    @19
    cc0
    @67
    @16
    fveq1
    eqeq2d
    imbi12d
    imbi2d
    cbvral2v
    sylib
    ancli
    @59
    @50
    @45
    @61
    wa
    #
    vb
    @0
    wral
    va
    @0
    wral
    @63
    @59
    @49
    @91
    va
    vb
    @0
    @0
    @59
    @55
    @56
    wa
    #
    wa
    #
    @49
    @44
    @60
    wo
    #
    @22
    wi
    @91
    @93
    @48
    @94
    @22
    @92
    @59
    @57
    @48
    @94
    wb
    #
    @55
    @57
    @56
    @58
    adantr
    @57
    @59
    @95
    @57
    @59
    wa
    @12
    @43
    cle
    wbr
    #
    @48
    @94
    @12
    @43
    nn0leltp1
    @57
    @12
    cr
    wcel
    @43
    cr
    wcel
    @96
    @94
    wb
    @59
    @12
    nn0re
    @43
    nn0re
    @12
    @43
    leloe
    syl2an
    bitr3d
    ancoms
    sylan2
    imbi1d
    @44
    @22
    @60
    jaob
    syl6bb
    2ralbidva
    @45
    @61
    va
    vb
    @0
    @0
    r19.26-2
    syl6bb
    syl5ibr
    nn0ind
    syl
    @9
    @13
    @9
    @13
    @37
    nn0red
    ltp1d
    @23
    @25
    @26
    wi
    @25
    @3
    @17
    wceq
    #
    @6
    @20
    wceq
    #
    wi
    #
    wi
    va
    vb
    cA
    cB
    @0
    @0
    @10
    cA
    wceq
    #
    @15
    @25
    @22
    @99
    @100
    @12
    @13
    @14
    clt
    @100
    @11
    @3
    chash
    @10
    cA
    cS
    fveq2
    #
    fveq2d
    breq1d
    @100
    @18
    @97
    @21
    @98
    @100
    @11
    @3
    @17
    @101
    eqeq1d
    @100
    @19
    @6
    @20
    cc0
    @10
    cA
    fveq1
    eqeq1d
    imbi12d
    imbi12d
    @16
    cB
    wceq
    #
    @99
    @26
    @25
    @102
    @97
    @5
    @98
    @8
    @102
    @17
    @4
    @3
    @16
    cB
    cS
    fveq2
    eqeq2d
    @102
    @20
    @7
    @6
    cc0
    @16
    cB
    fveq1
    eqeq2d
    imbi12d
    imbi2d
    rspc2v
    mp2d
    3impia
end
