include "cdm.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "cres.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "crn.mm"
include "wral.mm"
include "wne.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "adantr.mm"
include "eldifad.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "simpr.mm"
include "sseldi.mm"
include "swrd0val.mm"
include "syl2anc.mm"
include "swrdcl.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "cn.mm"
include "swrd0len.mm"
include "elfznn.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "cfn.mm"
include "wb.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "3syl.mm"
include "mpbid.mm"
include "eqnetrrd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "fvres.mm"
include "simp2bi.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "simp3bi.mm"
include "ssralv.mm"
include "sylc.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "cz.mm"
include "caddc.mm"
include "elfzoel2.mm"
include "peano2zm.mm"
include "uzid.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "peano2uzr.mm"
include "elfzoelz.mm"
include "elfzom1b.mm"
include "ibi.mm"
include "sseldd.mm"
include "rneqd.mm"
include "eleq12d.mm"
include "ralbiia.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "syl3anbrc.mm"

theorem efgsres
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
  let cN: class N
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
  assert |- ( ( F e. dom S /\ N e. ( 1 ... ( # ` F ) ) ) -> ( F |` ( 0 ..^ N ) ) e. dom S )

  proof
    cF
    cS
    cdm
    #
    wcel
    #
    cN
    c1
    cF
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cF
    cc0
    cN
    cfzo
    co
    #
    cres
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
    @7
    cfv
    #
    cD
    wcel
    vi
    cv
    #
    @7
    cfv
    #
    @13
    c1
    cmin
    co
    #
    @7
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
    @7
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @7
    @0
    wcel
    @5
    @7
    @8
    wcel
    @7
    c0
    wne
    @11
    @5
    cF
    cc0
    cN
    cop
    csubstr
    co
    #
    @7
    @8
    @5
    cF
    @8
    wcel
    #
    cN
    cc0
    @2
    cfz
    co
    #
    wcel
    #
    @23
    @7
    wceq
    @5
    cF
    @8
    @9
    @1
    cF
    @10
    wcel
    #
    @4
    @1
    @27
    cc0
    cF
    cfv
    #
    cD
    wcel
    #
    @13
    cF
    cfv
    #
    @15
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
    eldifad
    #
    @5
    @3
    @25
    cN
    c1
    cc0
    cuz
    cfv
    wcel
    @3
    @25
    wss
    1eluzge0
    c1
    cc0
    @2
    fzss1
    ax-mp
    @1
    @4
    simpr
    sseldi
    #
    cW
    cF
    cN
    swrd0val
    syl2anc
    #
    @5
    @24
    @23
    @8
    wcel
    #
    @38
    cW
    cF
    cc0
    cN
    swrdcl
    syl
    #
    eqeltrrd
    @5
    @23
    @7
    c0
    @40
    @5
    @23
    chash
    cfv
    #
    cn
    wcel
    #
    @23
    c0
    wne
    #
    @5
    @43
    cN
    cn
    @5
    @24
    @26
    @43
    cN
    wceq
    @38
    @39
    cW
    cF
    cN
    swrd0len
    syl2anc
    #
    @4
    cN
    cn
    wcel
    #
    @1
    cN
    @2
    elfznn
    adantl
    #
    eqeltrd
    @5
    @41
    @23
    cfn
    wcel
    @44
    @45
    wb
    @42
    cW
    @23
    wrdfin
    @23
    hashnncl
    3syl
    mpbid
    eqnetrrd
    @7
    @8
    c0
    eldifsn
    sylanbrc
    @5
    @12
    @28
    cD
    @5
    cc0
    @6
    wcel
    #
    @12
    @28
    wceq
    @5
    @47
    @49
    @48
    cN
    lbfzo0
    sylibr
    cc0
    @6
    cF
    fvres
    syl
    @1
    @29
    @4
    @1
    @27
    @29
    @36
    @37
    simp2bi
    adantr
    eqeltrd
    @5
    @22
    @19
    vi
    c1
    cN
    cfzo
    co
    #
    wral
    #
    @5
    @34
    vi
    @50
    wral
    #
    @51
    @5
    @50
    @35
    wss
    #
    @36
    @52
    @5
    @2
    cN
    cuz
    cfv
    #
    wcel
    #
    @53
    @4
    @55
    @1
    cN
    c1
    @2
    elfzuz3
    adantl
    cN
    c1
    @2
    fzoss2
    syl
    @1
    @36
    @4
    @1
    @27
    @29
    @36
    @37
    simp3bi
    adantr
    @34
    vi
    @50
    @35
    ssralv
    sylc
    @19
    @34
    vi
    @50
    @13
    @50
    wcel
    #
    @14
    @30
    @18
    @33
    @56
    @13
    @6
    wcel
    @14
    @30
    wceq
    @50
    @6
    @13
    cN
    fzo0ss1
    sseli
    @13
    @6
    cF
    fvres
    syl
    @56
    @17
    @32
    @56
    @16
    @31
    cT
    @56
    @15
    @6
    wcel
    @16
    @31
    wceq
    @56
    cc0
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    #
    @6
    @15
    @56
    cN
    @57
    cuz
    cfv
    wcel
    #
    @58
    @6
    wss
    @56
    @57
    cz
    wcel
    #
    cN
    @57
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @59
    @56
    cN
    cz
    wcel
    #
    @60
    @13
    c1
    cN
    elfzoel2
    #
    cN
    peano2zm
    syl
    @56
    cN
    @54
    @62
    @56
    @63
    cN
    @54
    wcel
    @64
    cN
    uzid
    syl
    @56
    @61
    cN
    cuz
    @56
    cN
    cc
    wcel
    c1
    cc
    wcel
    @61
    cN
    wceq
    @56
    cN
    @64
    zcnd
    ax-1cn
    cN
    c1
    npcan
    sylancl
    fveq2d
    eleqtrrd
    @57
    cN
    peano2uzr
    syl2anc
    @57
    cc0
    cN
    fzoss2
    syl
    @56
    @15
    @58
    wcel
    #
    @56
    @13
    cz
    wcel
    @63
    @56
    @65
    wb
    @13
    c1
    cN
    elfzoelz
    @64
    @13
    cN
    elfzom1b
    syl2anc
    ibi
    sseldd
    @15
    @6
    cF
    fvres
    syl
    fveq2d
    rneqd
    eleq12d
    ralbiia
    sylibr
    @5
    @19
    vi
    @21
    @50
    @5
    @20
    cN
    c1
    cfzo
    @5
    @43
    @20
    cN
    @5
    @23
    @7
    chash
    @40
    fveq2d
    @46
    eqtr3d
    oveq2d
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
    @7
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
