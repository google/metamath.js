include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wbr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "cv.mm"
include "crn.mm"
include "wral.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "lennncl.mm"
include "sylbi.mm"
include "fzo0end.mm"
include "3syl.mm"
include "cn0.mm"
include "wi.mm"
include "nnm1nn0.mm"
include "caddc.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "wf.mm"
include "eldifi.mm"
include "wrdf.mm"
include "ffvelrnda.mm"
include "erref.mm"
include "ex.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "peano2fzor.mm"
include "sylanb.mm"
include "3adant1.mm"
include "3expia.mm"
include "imim1d.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "ffvelrnd.mm"
include "nn0p1nn.mm"
include "3ad2ant2.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "elfzolt2b.mm"
include "3ad2ant3.mm"
include "elfzo3.mm"
include "sylanbrc.mm"
include "simp3bi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "rneqd.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eleqtrd.mm"
include "efgi2.mm"
include "syl2anc.mm"
include "ertr.mm"
include "mpan2d.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "nn0ind.mm"
include "mpcom.mm"
include "mpd.mm"
include "efgsval.mm"
include "breqtrrd.mm"

theorem efgsrel
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
  let cA: class A
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
  assert |- ( F e. dom S -> ( F ` 0 ) .~ ( S ` F ) )

  proof
    cF
    cS
    cdm
    wcel
    #
    cc0
    cF
    cfv
    #
    cF
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cF
    cS
    cfv
    c.sm
    @0
    @3
    cc0
    @2
    cfzo
    co
    #
    wcel
    #
    @1
    @4
    c.sm
    wbr
    #
    @0
    cF
    cW
    cword
    #
    c0
    csn
    #
    cdif
    wcel
    #
    @2
    cn
    wcel
    #
    @6
    @0
    @10
    @1
    cD
    wcel
    #
    va
    cv
    #
    cF
    cfv
    #
    @13
    c1
    cmin
    co
    #
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
    va
    c1
    @2
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
    va
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
    #
    @10
    cF
    @8
    wcel
    #
    cF
    c0
    wne
    wa
    @11
    cF
    @8
    c0
    eldifsn
    cW
    cF
    lennncl
    sylbi
    #
    @2
    fzo0end
    3syl
    @3
    cn0
    wcel
    #
    @0
    @6
    @7
    wi
    #
    @0
    @10
    @11
    @26
    @23
    @25
    @2
    nnm1nn0
    3syl
    @0
    @13
    @5
    wcel
    #
    @1
    @14
    c.sm
    wbr
    #
    wi
    #
    wi
    @0
    cc0
    @5
    wcel
    #
    @1
    @1
    c.sm
    wbr
    #
    wi
    #
    wi
    @0
    vi
    cv
    #
    @5
    wcel
    #
    @1
    @34
    cF
    cfv
    #
    c.sm
    wbr
    #
    wi
    #
    wi
    @0
    @34
    c1
    caddc
    co
    #
    @5
    wcel
    #
    @1
    @39
    cF
    cfv
    #
    c.sm
    wbr
    #
    wi
    #
    wi
    @0
    @27
    wi
    va
    vi
    @3
    @13
    cc0
    wceq
    #
    @30
    @33
    @0
    @44
    @28
    @31
    @29
    @32
    @13
    cc0
    @5
    eleq1
    @44
    @14
    @1
    @1
    c.sm
    @13
    cc0
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @13
    @34
    wceq
    #
    @30
    @38
    @0
    @45
    @28
    @35
    @29
    @37
    @13
    @34
    @5
    eleq1
    @45
    @14
    @36
    @1
    c.sm
    @13
    @34
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @13
    @39
    wceq
    #
    @30
    @43
    @0
    @46
    @28
    @40
    @29
    @42
    @13
    @39
    @5
    eleq1
    @46
    @14
    @41
    @1
    c.sm
    @13
    @39
    cF
    fveq2
    #
    breq2d
    imbi12d
    imbi2d
    @13
    @3
    wceq
    #
    @30
    @27
    @0
    @48
    @28
    @6
    @29
    @7
    @13
    @3
    @5
    eleq1
    @48
    @14
    @4
    @1
    c.sm
    @13
    @3
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @0
    @31
    @32
    @0
    @31
    wa
    #
    @1
    c.sm
    cW
    cW
    c.sm
    wer
    #
    @49
    c.sm
    cI
    cW
    efgval.w
    efgval.r
    efger
    #
    a1i
    @0
    @5
    cW
    cc0
    cF
    @0
    @10
    @24
    @5
    cW
    cF
    wf
    #
    @23
    cF
    @8
    @9
    eldifi
    cW
    cF
    wrdf
    3syl
    #
    ffvelrnda
    erref
    ex
    @34
    cn0
    wcel
    #
    @0
    @38
    @43
    @0
    @54
    @38
    @43
    wi
    @0
    @54
    wa
    #
    @38
    @40
    @37
    wi
    @43
    @55
    @40
    @35
    @37
    @0
    @54
    @40
    @35
    @54
    @40
    @35
    @0
    @54
    @34
    cc0
    cuz
    cfv
    wcel
    @40
    @35
    @34
    elnn0uz
    @34
    cc0
    @2
    peano2fzor
    sylanb
    3adant1
    #
    3expia
    imim1d
    @55
    @40
    @37
    @42
    @0
    @54
    @40
    @37
    @42
    wi
    @0
    @54
    @40
    w3a
    #
    @37
    @36
    @41
    c.sm
    wbr
    #
    @42
    @57
    @36
    cW
    wcel
    @41
    @36
    cT
    cfv
    #
    crn
    #
    wcel
    @58
    @57
    @5
    cW
    @34
    cF
    @0
    @54
    @52
    @40
    @53
    3ad2ant1
    @56
    ffvelrnd
    @57
    @41
    @39
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cT
    cfv
    #
    crn
    #
    @60
    @57
    @39
    @20
    wcel
    #
    @21
    @41
    @64
    wcel
    #
    @57
    @39
    c1
    cuz
    cfv
    #
    wcel
    @39
    @39
    @2
    cfzo
    co
    wcel
    #
    @65
    @57
    @39
    cn
    @67
    @54
    @0
    @39
    cn
    wcel
    @40
    @34
    nn0p1nn
    3ad2ant2
    nnuz
    syl6eleq
    @40
    @0
    @68
    @54
    @39
    cc0
    @2
    elfzolt2b
    3ad2ant3
    @39
    c1
    @2
    elfzo3
    sylanbrc
    @0
    @54
    @21
    @40
    @0
    @10
    @12
    @21
    @22
    simp3bi
    3ad2ant1
    @19
    @66
    va
    @39
    @20
    @46
    @14
    @41
    @18
    @64
    @47
    @46
    @17
    @63
    @46
    @16
    @62
    cT
    @46
    @15
    @61
    cF
    @13
    @39
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    rneqd
    eleq12d
    rspcv
    sylc
    @57
    @63
    @59
    @57
    @62
    @36
    cT
    @57
    @61
    @34
    cF
    @57
    @34
    cc
    wcel
    #
    c1
    cc
    wcel
    @61
    @34
    wceq
    @54
    @0
    @69
    @40
    @34
    nn0cn
    3ad2ant2
    ax-1cn
    @34
    c1
    pncan
    sylancl
    fveq2d
    fveq2d
    rneqd
    eleqtrd
    vy
    vz
    vw
    vv
    @36
    @41
    c.sm
    cT
    vn
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgi2
    syl2anc
    @57
    @1
    @36
    @41
    c.sm
    cW
    @50
    @57
    @51
    a1i
    ertr
    mpan2d
    3expia
    a2d
    syld
    expcom
    a2d
    nn0ind
    mpcom
    mpd
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
    breqtrrd
end
