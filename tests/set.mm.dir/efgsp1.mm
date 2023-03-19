include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wne.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "adantr.mm"
include "eldifad.mm"
include "cfz.mm"
include "c2o.mm"
include "cxp.mm"
include "wf.mm"
include "wss.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "wceq.mm"
include "crab.mm"
include "efgsf.mm"
include "fdmi.mm"
include "feq2i.mm"
include "mpbir.mm"
include "ffvelrni.mm"
include "efgtf.mm"
include "syl.mm"
include "simprd.mm"
include "frn.mm"
include "simpr.mm"
include "sseldd.mm"
include "s1cld.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "cn.mm"
include "caddc.mm"
include "ccatlen.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "cfn.mm"
include "wb.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "mpbid.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eldifsni.mm"
include "mpbird.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "simp2bi.mm"
include "cun.mm"
include "simp3bi.mm"
include "w3a.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "syl3an3.mm"
include "cuz.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "elfzoel2.mm"
include "peano2zm.mm"
include "zred.mm"
include "lem1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "elfzoelz.mm"
include "elfzom1b.mm"
include "ibi.mm"
include "fveq2d.mm"
include "rneqd.mm"
include "eleq12d.mm"
include "3expa.mm"
include "ralbidva.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "1nn.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ccatval3.mm"
include "eqtr3d.mm"
include "s1fv.mm"
include "adantl.mm"
include "fzo0end.mm"
include "efgsval.mm"
include "eqtr4d.mm"
include "3eltr4d.mm"
include "fvex.mm"
include "fveq2.mm"
include "oveq1.mm"
include "ralsn.mm"
include "ralunb.mm"
include "oveq2d.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"
include "raleqdv.mm"

theorem efgsp1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cD: class D
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
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
  assert |- ( ( F e. dom S /\ A e. ran ( T ` ( S ` F ) ) ) -> ( F ++ <" A "> ) e. dom S )

  proof
    cF
    cS
    cdm
    #
    wcel
    #
    cA
    cF
    cS
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    wa
    #
    cF
    cA
    cs1
    #
    cconcat
    co
    #
    cW
    cword
    #
    c0
    csn
    #
    cdif
    #
    wcel
    #
    cc0
    @8
    cfv
    #
    cD
    wcel
    vi
    cv
    #
    @8
    cfv
    #
    @14
    c1
    cmin
    co
    #
    @8
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vi
    c1
    @8
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @8
    @0
    wcel
    @6
    @8
    @9
    wcel
    #
    @8
    c0
    wne
    #
    @12
    @6
    cF
    @9
    wcel
    #
    @7
    @9
    wcel
    #
    @24
    @6
    cF
    @9
    @10
    @1
    cF
    @11
    wcel
    #
    @5
    @1
    @28
    cc0
    cF
    cfv
    #
    cD
    wcel
    #
    @14
    cF
    cfv
    #
    @16
    cF
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vi
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
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
    vi
    vk
    vm
    vn
    cF
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
    #
    simp1bi
    adantr
    #
    eldifad
    #
    @6
    cA
    cW
    @6
    @4
    cW
    cA
    @6
    cc0
    @2
    chash
    cfv
    cfz
    co
    #
    cI
    c2o
    cxp
    #
    cxp
    #
    cW
    @3
    wf
    #
    @4
    cW
    wss
    @6
    @3
    va
    vi
    @42
    @43
    @2
    va
    cv
    #
    @46
    @14
    @14
    cM
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    wceq
    #
    @45
    @6
    @2
    cW
    wcel
    #
    @47
    @45
    wa
    @1
    @48
    @5
    @0
    cW
    cF
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
    @49
    cfv
    @50
    c1
    cmin
    co
    @49
    cfv
    cT
    cfv
    crn
    wcel
    vk
    c1
    @49
    chash
    cfv
    cfzo
    co
    wral
    wa
    vt
    @11
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
    @51
    cW
    cS
    @51
    cW
    cS
    @52
    fdmi
    feq2i
    mpbir
    ffvelrni
    adantr
    vy
    vz
    vw
    vv
    c.sm
    cT
    vn
    cI
    cM
    cW
    @2
    va
    vi
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    syl
    simprd
    @44
    cW
    @3
    frn
    syl
    @1
    @5
    simpr
    #
    sseldd
    s1cld
    #
    cW
    cF
    @7
    ccatcl
    syl2anc
    #
    @6
    @21
    cn
    wcel
    #
    @25
    @6
    @21
    @36
    c1
    caddc
    co
    #
    cn
    @6
    @21
    @36
    @7
    chash
    cfv
    #
    caddc
    co
    #
    @57
    @6
    @26
    @27
    @21
    @59
    wceq
    @41
    @54
    cW
    cF
    @7
    ccatlen
    syl2anc
    @58
    c1
    @36
    caddc
    cA
    s1len
    #
    oveq2i
    syl6eq
    #
    @6
    @26
    @36
    cn0
    wcel
    #
    @57
    cn
    wcel
    @41
    cW
    cF
    lencl
    #
    @36
    nn0p1nn
    3syl
    eqeltrd
    @6
    @24
    @8
    cfn
    wcel
    @56
    @25
    wb
    @55
    cW
    @8
    wrdfin
    @8
    hashnncl
    3syl
    mpbid
    @8
    @9
    c0
    eldifsn
    sylanbrc
    @6
    @13
    @29
    cD
    @6
    @26
    @27
    cc0
    cc0
    @36
    cfzo
    co
    #
    wcel
    #
    @13
    @29
    wceq
    @41
    @54
    @6
    @36
    cn
    wcel
    #
    @65
    @6
    @66
    cF
    c0
    wne
    #
    @6
    @28
    @67
    @40
    cF
    @9
    c0
    eldifsni
    syl
    @6
    @26
    cF
    cfn
    wcel
    @66
    @67
    wb
    @41
    cW
    cF
    wrdfin
    cF
    hashnncl
    3syl
    mpbird
    #
    @36
    lbfzo0
    sylibr
    cW
    cF
    @7
    cc0
    ccatval1
    syl3anc
    @1
    @30
    @5
    @1
    @28
    @30
    @38
    @39
    simp2bi
    adantr
    eqeltrd
    @6
    @23
    @20
    vi
    @37
    @36
    csn
    #
    cun
    #
    wral
    #
    @6
    @20
    vi
    @37
    wral
    #
    @20
    vi
    @69
    wral
    #
    @71
    @6
    @72
    @38
    @1
    @38
    @5
    @1
    @28
    @30
    @38
    @39
    simp3bi
    adantr
    @6
    @26
    @27
    @72
    @38
    wb
    @41
    @54
    @26
    @27
    wa
    @20
    @35
    vi
    @37
    @26
    @27
    @14
    @37
    wcel
    #
    @20
    @35
    wb
    @26
    @27
    @74
    w3a
    #
    @15
    @31
    @19
    @34
    @74
    @26
    @27
    @14
    @64
    wcel
    @15
    @31
    wceq
    @37
    @64
    @14
    @36
    fzo0ss1
    sseli
    cW
    cF
    @7
    @14
    ccatval1
    syl3an3
    @75
    @18
    @33
    @75
    @17
    @32
    cT
    @74
    @26
    @27
    @16
    @64
    wcel
    @17
    @32
    wceq
    @74
    cc0
    @36
    c1
    cmin
    co
    #
    cfzo
    co
    #
    @64
    @16
    @74
    @36
    @76
    cuz
    cfv
    wcel
    #
    @77
    @64
    wss
    @74
    @76
    cz
    wcel
    #
    @36
    cz
    wcel
    #
    @76
    @36
    cle
    wbr
    @78
    @74
    @80
    @79
    @14
    c1
    @36
    elfzoel2
    #
    @36
    peano2zm
    syl
    @81
    @74
    @36
    @74
    @36
    @81
    zred
    lem1d
    @76
    @36
    eluz2
    syl3anbrc
    @76
    cc0
    @36
    fzoss2
    syl
    @74
    @16
    @77
    wcel
    #
    @74
    @14
    cz
    wcel
    @80
    @74
    @82
    wb
    @14
    c1
    @36
    elfzoelz
    @81
    @14
    @36
    elfzom1b
    syl2anc
    ibi
    sseldd
    cW
    cF
    @7
    @16
    ccatval1
    syl3an3
    fveq2d
    rneqd
    eleq12d
    3expa
    ralbidva
    syl2anc
    mpbird
    @6
    @36
    @8
    cfv
    #
    @76
    @8
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    @73
    @6
    @83
    cc0
    @7
    cfv
    #
    @86
    @6
    cc0
    @36
    caddc
    co
    #
    @8
    cfv
    #
    @83
    @88
    @6
    @89
    @36
    @8
    @6
    @36
    @6
    @36
    @6
    @26
    @62
    @41
    @63
    syl
    nn0cnd
    addid2d
    fveq2d
    @6
    @26
    @27
    cc0
    cc0
    @58
    cfzo
    co
    wcel
    #
    @90
    @88
    wceq
    @41
    @54
    @6
    @58
    cn
    wcel
    #
    @91
    @92
    @6
    @58
    c1
    cn
    @60
    1nn
    eqeltri
    a1i
    @58
    lbfzo0
    sylibr
    cW
    cF
    @7
    cc0
    ccatval3
    syl3anc
    eqtr3d
    @6
    cA
    @4
    @88
    @86
    @53
    @5
    @88
    cA
    wceq
    @1
    cA
    @4
    s1fv
    adantl
    @6
    @85
    @3
    @6
    @84
    @2
    cT
    @6
    @84
    @76
    cF
    cfv
    #
    @2
    @6
    @26
    @27
    @76
    @64
    wcel
    #
    @84
    @93
    wceq
    @41
    @54
    @6
    @66
    @94
    @68
    @36
    fzo0end
    syl
    cW
    cF
    @7
    @76
    ccatval1
    syl3anc
    @1
    @2
    @93
    wceq
    @5
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
    cF
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
    adantr
    eqtr4d
    fveq2d
    rneqd
    3eltr4d
    eqeltrd
    @20
    @87
    vi
    @36
    cF
    chash
    fvex
    @14
    @36
    wceq
    #
    @15
    @83
    @19
    @86
    @14
    @36
    @8
    fveq2
    @95
    @18
    @85
    @95
    @17
    @84
    cT
    @95
    @16
    @76
    @8
    @14
    @36
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    rneqd
    eleq12d
    ralsn
    sylibr
    @20
    vi
    @37
    @69
    ralunb
    sylanbrc
    @6
    @20
    vi
    @22
    @70
    @6
    @22
    c1
    @57
    cfzo
    co
    #
    @70
    @6
    @21
    @57
    c1
    cfzo
    @61
    oveq2d
    @6
    @36
    c1
    cuz
    cfv
    #
    wcel
    @96
    @70
    wceq
    @6
    @36
    cn
    @97
    @68
    nnuz
    syl6eleq
    c1
    @36
    fzosplitsn
    syl
    eqtrd
    raleqdv
    mpbird
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
    @8
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
    syl3anbrc
end
