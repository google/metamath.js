include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "co.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "c2.mm"
include "caddc.mm"
include "chash.mm"
include "cfz.mm"
include "c2o.mm"
include "cxp.mm"
include "wceq.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
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
include "ffvelrni.mm"
include "syl.mm"
include "cuz.mm"
include "elfzuz.mm"
include "fveq2d.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "efgredlemf.mm"
include "simprd.mm"
include "sseldi.mm"
include "swrdcl.mm"
include "simpld.mm"
include "ccatlen.mm"
include "syl2anc.mm"
include "swrd0len.mm"
include "cn0.mm"
include "2nn0.mm"
include "uzaddcl.mm"
include "sylancl.mm"
include "elfzuz3.mm"
include "uztrn.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "lencl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "cz.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "nn0cnd.mm"
include "2z.mm"
include "zaddcl.mm"
include "addsubassd.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "pnpcand.mm"
include "3eqtr2d.mm"
include "3eqtrd.mm"
include "zsubcl.mm"
include "npcan.mm"
include "eleqtrrd.mm"
include "eluzsub.mm"
include "eqeltrd.mm"
include "efgtval.mm"
include "wrd0.mm"
include "efgmf.mm"
include "s2cld.mm"
include "eluzfz1.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "zred.mm"
include "nn0addge1.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "ccatass.mm"
include "splval.mm"
include "3eqtr3d.mm"
include "ccatcl.mm"
include "wb.mm"
include "eqtr4d.mm"
include "ccatopth.mm"
include "syl221anc.mm"
include "mpbid.mm"
include "ccatrid.mm"
include "3eqtr4rd.mm"
include "eqcomd.mm"
include "hash0.mm"
include "oveq2i.mm"
include "addid1d.mm"
include "syl5req.mm"
include "splval2.mm"
include "pncan2.mm"
include "eqtrd.mm"
include "s2len.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "swrdid.mm"
include "wfn.mm"
include "cmpt2.mm"
include "efgtf.mm"
include "ffn.mm"
include "fnovrn.mm"
include "eqeltrrd.mm"
include "efgredlemg.mm"
include "0le2.mm"
include "2re.mm"
include "subge02.mm"
include "sub32d.mm"
include "subsub4d.mm"
include "nncan.mm"
include "eqtr2d.mm"
include "syl5eq.mm"
include "jca.mm"

theorem efgredleme
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cV: class V
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
  let cF: class F
  let cN: class N
  let vo: setvar o
  let cX: class X
  let cY: class Y
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )
  assume efgval2.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume efgval2.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume efgred.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume efgred.s: |- S = ( m e. { t e. ( Word W \ { (/) } ) | ( ( t ` 0 ) e. D /\ A. k e. ( 1 ..^ ( # ` t ) ) ( t ` k ) e. ran ( T ` ( t ` ( k - 1 ) ) ) ) } |-> ( m ` ( ( # ` m ) - 1 ) ) )
  assume efgredlem.1: |- ( ph -> A. a e. dom S A. b e. dom S ( ( # ` ( S ` a ) ) < ( # ` ( S ` A ) ) -> ( ( S ` a ) = ( S ` b ) -> ( a ` 0 ) = ( b ` 0 ) ) ) )
  assume efgredlem.2: |- ( ph -> A e. dom S )
  assume efgredlem.3: |- ( ph -> B e. dom S )
  assume efgredlem.4: |- ( ph -> ( S ` A ) = ( S ` B ) )
  assume efgredlem.5: |- ( ph -> -. ( A ` 0 ) = ( B ` 0 ) )
  assume efgredlemb.k: |- K = ( ( ( # ` A ) - 1 ) - 1 )
  assume efgredlemb.l: |- L = ( ( ( # ` B ) - 1 ) - 1 )
  assume efgredlemb.p: |- ( ph -> P e. ( 0 ... ( # ` ( A ` K ) ) ) )
  assume efgredlemb.q: |- ( ph -> Q e. ( 0 ... ( # ` ( B ` L ) ) ) )
  assume efgredlemb.u: |- ( ph -> U e. ( I X. 2o ) )
  assume efgredlemb.v: |- ( ph -> V e. ( I X. 2o ) )
  assume efgredlemb.6: |- ( ph -> ( S ` A ) = ( P ( T ` ( A ` K ) ) U ) )
  assume efgredlemb.7: |- ( ph -> ( S ` B ) = ( Q ( T ` ( B ` L ) ) V ) )
  assume efgredlemb.8: |- ( ph -> -. ( A ` K ) = ( B ` L ) )
  assume efgredlemd.9: |- ( ph -> P e. ( ZZ>= ` ( Q + 2 ) ) )
  assume efgredlemd.c: |- ( ph -> C e. dom S )
  assume efgredlemd.sc: |- ( ph -> ( S ` C ) = ( ( ( B ` L ) substr <. 0 , Q >. ) ++ ( ( A ` K ) substr <. ( Q + 2 ) , ( # ` ( A ` K ) ) >. ) ) )

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint a z
  disjoint b y
  disjoint b z
  disjoint y z
  disjoint L a
  disjoint L b
  disjoint K a
  disjoint K b
  disjoint n t
  disjoint n v
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint P n
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint P t
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint P y
  disjoint P z
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
  disjoint U n
  disjoint U v
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint a k
  disjoint T a
  disjoint b k
  disjoint T b
  disjoint k m
  disjoint k t
  disjoint k x
  disjoint T k
  disjoint T m
  disjoint T t
  disjoint T x
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint Q n
  disjoint Q t
  disjoint Q v
  disjoint Q w
  disjoint Q y
  disjoint Q z
  disjoint W a
  disjoint W b
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
  disjoint .~ a
  disjoint .~ b
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
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
  disjoint I a
  disjoint I b
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint D a
  disjoint D b
  disjoint D m
  disjoint D t
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
  disjoint J a
  disjoint J b
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint J y
  disjoint J z
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
  disjoint K c
  disjoint K r
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint P c
  disjoint c ph
  disjoint i ph
  disjoint j ph
  disjoint ph r
  disjoint ph s
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
  disjoint a o
  disjoint b o
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
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint X u
  disjoint Q c
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
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ i
  disjoint .~ j
  disjoint .~ r
  disjoint .~ s
  disjoint .~ u
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
  disjoint C i
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
  disjoint I c
  disjoint I f
  disjoint I g
  disjoint I i
  disjoint I j
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- ( ph -> ( ( A ` K ) e. ran ( T ` ( S ` C ) ) /\ ( B ` L ) e. ran ( T ` ( S ` C ) ) ) )

  proof
    wph
    cK
    cA
    cfv
    #
    cC
    cS
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    cL
    cB
    cfv
    #
    @3
    wcel
    wph
    cQ
    cV
    @2
    co
    #
    @0
    @3
    wph
    @5
    @1
    cQ
    cQ
    cV
    cV
    cM
    cfv
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    @0
    cc0
    cQ
    cop
    #
    csubstr
    co
    #
    @7
    cconcat
    co
    #
    @0
    cQ
    c2
    caddc
    co
    #
    @0
    chash
    cfv
    #
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    @0
    wph
    @1
    cW
    wcel
    #
    cQ
    cc0
    @1
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    cV
    cI
    c2o
    cxp
    #
    wcel
    #
    @5
    @9
    wceq
    wph
    cC
    cS
    cdm
    #
    wcel
    @17
    efgredlemd.c
    @23
    cW
    cC
    cS
    @23
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
    @24
    cfv
    @25
    c1
    cmin
    co
    @24
    cfv
    cT
    cfv
    crn
    wcel
    vk
    c1
    @24
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
    @23
    @26
    cW
    cS
    @26
    cW
    cS
    @27
    fdmi
    feq2i
    mpbir
    ffvelrni
    syl
    #
    wph
    cQ
    cc0
    cuz
    cfv
    #
    wcel
    #
    @18
    cQ
    cuz
    cfv
    #
    wcel
    #
    @20
    wph
    cQ
    cc0
    @4
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @30
    efgredlemb.q
    cQ
    cc0
    @33
    elfzuz
    syl
    #
    wph
    @18
    cP
    c2
    cmin
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @37
    @31
    wcel
    #
    @32
    wph
    @18
    @14
    c2
    cmin
    co
    #
    @38
    wph
    @18
    @4
    @10
    csubstr
    co
    #
    @15
    cconcat
    co
    #
    chash
    cfv
    #
    @42
    chash
    cfv
    #
    @15
    chash
    cfv
    #
    caddc
    co
    #
    @41
    wph
    @1
    @43
    chash
    efgredlemd.sc
    fveq2d
    wph
    @42
    @21
    cword
    #
    wcel
    #
    @15
    @48
    wcel
    #
    @44
    @47
    wceq
    wph
    @4
    @48
    wcel
    #
    @49
    wph
    cW
    @48
    @4
    cW
    @48
    cid
    cfv
    @48
    efgval.w
    @48
    fviss
    eqsstri
    #
    wph
    @0
    cW
    wcel
    #
    @4
    cW
    wcel
    #
    wph
    vx
    vy
    vz
    vw
    vv
    vt
    cA
    cB
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cI
    cK
    cL
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
    efgredlem.1
    efgredlem.2
    efgredlem.3
    efgredlem.4
    efgredlem.5
    efgredlemb.k
    efgredlemb.l
    efgredlemf
    #
    simprd
    #
    sseldi
    #
    @21
    @4
    cc0
    cQ
    swrdcl
    syl
    #
    wph
    @0
    @48
    wcel
    #
    @50
    wph
    cW
    @48
    @0
    @52
    wph
    @53
    @54
    @55
    simpld
    #
    sseldi
    #
    @21
    @0
    @13
    @14
    swrdcl
    syl
    #
    @21
    @42
    @15
    ccatlen
    syl2anc
    wph
    @47
    cQ
    @14
    @13
    cmin
    co
    #
    caddc
    co
    cQ
    @14
    caddc
    co
    @13
    cmin
    co
    @41
    wph
    @45
    cQ
    @46
    @63
    caddc
    wph
    @51
    @35
    @45
    cQ
    wceq
    @57
    efgredlemb.q
    @21
    @4
    cQ
    swrd0len
    syl2anc
    #
    wph
    @59
    @13
    cc0
    @14
    cfz
    co
    #
    wcel
    #
    @14
    @65
    wcel
    #
    @46
    @63
    wceq
    @61
    wph
    @13
    @29
    wcel
    #
    @14
    @13
    cuz
    cfv
    #
    wcel
    #
    @66
    wph
    @30
    c2
    cn0
    wcel
    #
    @68
    @36
    2nn0
    c2
    cc0
    cQ
    uzaddcl
    sylancl
    #
    wph
    @14
    cP
    cuz
    cfv
    #
    wcel
    #
    cP
    @69
    wcel
    #
    @70
    wph
    cP
    @65
    wcel
    #
    @74
    efgredlemb.p
    cP
    cc0
    @14
    elfzuz3
    syl
    #
    efgredlemd.9
    cP
    @14
    @13
    uztrn
    syl2anc
    @13
    cc0
    @14
    elfzuzb
    sylanbrc
    #
    wph
    @14
    @29
    wcel
    @67
    wph
    @14
    cn0
    @29
    wph
    @59
    @14
    cn0
    wcel
    @61
    @21
    @0
    lencl
    syl
    #
    nn0uz
    syl6eleq
    cc0
    @14
    eluzfz2
    syl
    #
    @21
    @0
    @13
    @14
    swrdlen
    syl3anc
    oveq12d
    wph
    cQ
    @14
    @13
    wph
    cQ
    wph
    @35
    cQ
    cz
    wcel
    #
    efgredlemb.q
    cQ
    cc0
    @33
    elfzelz
    syl
    #
    zcnd
    #
    wph
    @14
    @79
    nn0cnd
    #
    wph
    @13
    wph
    @81
    c2
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    @82
    2z
    cQ
    c2
    zaddcl
    sylancl
    #
    zcnd
    addsubassd
    wph
    cQ
    @14
    c2
    @83
    @84
    c2
    cc
    wcel
    #
    wph
    2cn
    a1i
    #
    pnpcand
    3eqtr2d
    3eqtrd
    wph
    @37
    cz
    wcel
    #
    @85
    @14
    @37
    c2
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @41
    @38
    wcel
    wph
    cP
    cz
    wcel
    #
    @85
    @90
    wph
    @76
    @93
    efgredlemb.p
    cP
    cc0
    @14
    elfzelz
    syl
    #
    2z
    cP
    c2
    zsubcl
    sylancl
    #
    @85
    wph
    2z
    a1i
    #
    wph
    @14
    @73
    @92
    @77
    wph
    @91
    cP
    cuz
    wph
    cP
    cc
    wcel
    #
    @88
    @91
    cP
    wceq
    wph
    cP
    @94
    zcnd
    #
    2cn
    cP
    c2
    npcan
    sylancl
    fveq2d
    eleqtrrd
    c2
    @37
    @14
    eluzsub
    syl3anc
    eqeltrd
    #
    wph
    @81
    @85
    @75
    @40
    @82
    @96
    efgredlemd.9
    c2
    cQ
    cP
    eluzsub
    syl3anc
    #
    @37
    @18
    cQ
    uztrn
    syl2anc
    cQ
    cc0
    @18
    elfzuzb
    sylanbrc
    #
    efgredlemb.v
    vy
    vz
    vw
    vv
    cV
    c.sm
    cT
    vn
    cI
    cM
    cQ
    cW
    @1
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    wph
    @11
    c0
    @15
    @7
    @1
    cQ
    cQ
    @21
    wph
    @59
    @11
    @48
    wcel
    #
    @61
    @21
    @0
    cc0
    cQ
    swrdcl
    syl
    #
    c0
    @48
    wcel
    wph
    @21
    wrd0
    a1i
    #
    @62
    wph
    cV
    @6
    @21
    efgredlemb.v
    wph
    @22
    @6
    @21
    wcel
    efgredlemb.v
    @21
    @21
    cV
    cM
    vy
    vz
    cI
    cM
    efgval2.m
    efgmf
    #
    ffvelrni
    syl
    s2cld
    #
    wph
    @11
    @15
    cconcat
    co
    @43
    @11
    c0
    cconcat
    co
    #
    @15
    cconcat
    co
    @1
    wph
    @11
    @42
    @15
    cconcat
    wph
    @11
    @42
    wceq
    #
    @0
    cQ
    cP
    cop
    csubstr
    co
    #
    cU
    cU
    cM
    cfv
    #
    cs2
    #
    @0
    cP
    @14
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cconcat
    co
    #
    @7
    @4
    cQ
    @33
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    wceq
    #
    wph
    @11
    @114
    cconcat
    co
    #
    @42
    @116
    cconcat
    co
    #
    wceq
    #
    @108
    @117
    wa
    #
    wph
    @11
    @109
    cconcat
    co
    #
    @113
    cconcat
    co
    #
    @42
    @7
    cconcat
    co
    @115
    cconcat
    co
    #
    @118
    @119
    wph
    @123
    @0
    cc0
    cP
    cop
    #
    csubstr
    co
    #
    @113
    cconcat
    co
    #
    @126
    @111
    cconcat
    co
    @112
    cconcat
    co
    #
    @124
    wph
    @122
    @126
    @113
    cconcat
    wph
    @59
    cc0
    cc0
    cQ
    cfz
    co
    wcel
    #
    cQ
    cc0
    cP
    cfz
    co
    #
    wcel
    #
    @76
    @122
    @126
    wceq
    @61
    wph
    @30
    @129
    @36
    cc0
    cQ
    eluzfz1
    syl
    #
    wph
    @30
    cP
    @31
    wcel
    #
    @131
    @36
    wph
    @75
    @13
    @31
    wcel
    #
    @133
    efgredlemd.9
    wph
    @81
    @86
    cQ
    @13
    cle
    wbr
    #
    @134
    @82
    @87
    wph
    cQ
    cr
    wcel
    @71
    @135
    wph
    cQ
    @82
    zred
    2nn0
    cQ
    c2
    nn0addge1
    sylancl
    cQ
    @13
    eluz2
    syl3anbrc
    #
    @13
    cP
    cQ
    uztrn
    syl2anc
    #
    cQ
    cc0
    cP
    elfzuzb
    sylanbrc
    efgredlemb.p
    @21
    @0
    cc0
    cQ
    cP
    ccatswrd
    syl13anc
    oveq1d
    wph
    @126
    @48
    wcel
    #
    @111
    @48
    wcel
    #
    @112
    @48
    wcel
    #
    @128
    @127
    wceq
    wph
    @59
    @138
    @61
    @21
    @0
    cc0
    cP
    swrdcl
    syl
    wph
    cU
    @110
    @21
    efgredlemb.u
    wph
    cU
    @21
    wcel
    #
    @110
    @21
    wcel
    efgredlemb.u
    @21
    @21
    cU
    cM
    @105
    ffvelrni
    syl
    s2cld
    #
    wph
    @59
    @140
    @61
    @21
    @0
    cP
    @14
    swrdcl
    syl
    #
    @21
    @126
    @111
    @112
    ccatass
    syl3anc
    wph
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    @128
    @124
    efgredlem.4
    wph
    @144
    cP
    cU
    @0
    cT
    cfv
    co
    #
    @0
    cP
    cP
    @111
    cotp
    csplice
    co
    #
    @128
    efgredlemb.6
    wph
    @53
    @76
    @141
    @146
    @147
    wceq
    @60
    efgredlemb.p
    efgredlemb.u
    vy
    vz
    vw
    vv
    cU
    c.sm
    cT
    vn
    cI
    cM
    cP
    cW
    @0
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    wph
    @53
    @76
    @76
    @139
    @147
    @128
    wceq
    @60
    efgredlemb.p
    efgredlemb.p
    @142
    @111
    @0
    cP
    cP
    cW
    @65
    @65
    @48
    splval
    syl13anc
    3eqtrd
    wph
    @145
    cQ
    cV
    @4
    cT
    cfv
    co
    #
    @4
    @8
    csplice
    co
    #
    @124
    efgredlemb.7
    wph
    @54
    @35
    @22
    @148
    @149
    wceq
    @56
    efgredlemb.q
    efgredlemb.v
    vy
    vz
    vw
    vv
    cV
    c.sm
    cT
    vn
    cI
    cM
    cQ
    cW
    @4
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    wph
    @54
    @35
    @35
    @7
    @48
    wcel
    #
    @149
    @124
    wceq
    @56
    efgredlemb.q
    efgredlemb.q
    @106
    @7
    @4
    cQ
    cQ
    cW
    @34
    @34
    @48
    splval
    syl13anc
    3eqtrd
    3eqtr3d
    3eqtr2d
    wph
    @102
    @109
    @48
    wcel
    #
    @113
    @48
    wcel
    #
    @123
    @118
    wceq
    @103
    wph
    @59
    @151
    @61
    @21
    @0
    cQ
    cP
    swrdcl
    syl
    #
    wph
    @139
    @140
    @152
    @142
    @143
    @21
    @111
    @112
    ccatcl
    syl2anc
    #
    @21
    @11
    @109
    @113
    ccatass
    syl3anc
    wph
    @49
    @150
    @115
    @48
    wcel
    #
    @124
    @119
    wceq
    @58
    @106
    wph
    @51
    @155
    @57
    @21
    @4
    cQ
    @33
    swrdcl
    syl
    #
    @21
    @42
    @7
    @115
    ccatass
    syl3anc
    3eqtr3d
    wph
    @102
    @114
    @48
    wcel
    #
    @49
    @116
    @48
    wcel
    #
    @11
    chash
    cfv
    #
    @45
    wceq
    @120
    @121
    wb
    @103
    wph
    @151
    @152
    @157
    @153
    @154
    @21
    @109
    @113
    ccatcl
    syl2anc
    @58
    wph
    @150
    @155
    @158
    @106
    @156
    @21
    @7
    @115
    ccatcl
    syl2anc
    wph
    @159
    cQ
    @45
    wph
    @59
    cQ
    @65
    wcel
    #
    @159
    cQ
    wceq
    @61
    wph
    @30
    @14
    @31
    wcel
    #
    @160
    @36
    wph
    @74
    @133
    @161
    @77
    @137
    cP
    @14
    cQ
    uztrn
    syl2anc
    cQ
    cc0
    @14
    elfzuzb
    sylanbrc
    @21
    @0
    cQ
    swrd0len
    syl2anc
    #
    @64
    eqtr4d
    @11
    @114
    @42
    @116
    @21
    ccatopth
    syl221anc
    mpbid
    #
    simpld
    oveq1d
    wph
    @107
    @11
    @15
    cconcat
    wph
    @102
    @107
    @11
    wceq
    @103
    @21
    @11
    ccatrid
    syl
    oveq1d
    efgredlemd.sc
    3eqtr4rd
    wph
    @159
    cQ
    @162
    eqcomd
    wph
    cQ
    c0
    chash
    cfv
    #
    caddc
    co
    cQ
    cc0
    caddc
    co
    cQ
    @164
    cc0
    cQ
    caddc
    hash0
    oveq2i
    wph
    cQ
    @83
    addid1d
    syl5req
    splval2
    wph
    @16
    @0
    cc0
    @13
    cop
    csubstr
    co
    #
    @15
    cconcat
    co
    #
    @0
    cc0
    @14
    cop
    csubstr
    co
    #
    @0
    wph
    @12
    @165
    @15
    cconcat
    wph
    @11
    @0
    cQ
    @13
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    @12
    @165
    wph
    @168
    @7
    @11
    cconcat
    wph
    @168
    @7
    wceq
    #
    @0
    @13
    cP
    cop
    csubstr
    co
    #
    @113
    cconcat
    co
    #
    @115
    wceq
    #
    wph
    @168
    @172
    cconcat
    co
    #
    @116
    wceq
    #
    @170
    @173
    wa
    #
    wph
    @168
    @171
    cconcat
    co
    #
    @113
    cconcat
    co
    #
    @114
    @174
    @116
    wph
    @177
    @109
    @113
    cconcat
    wph
    @59
    cQ
    cc0
    @13
    cfz
    co
    #
    wcel
    #
    @13
    @130
    wcel
    #
    @76
    @177
    @109
    wceq
    @61
    wph
    @30
    @134
    @180
    @36
    @136
    cQ
    cc0
    @13
    elfzuzb
    sylanbrc
    #
    wph
    @68
    @75
    @181
    @72
    efgredlemd.9
    @13
    cc0
    cP
    elfzuzb
    sylanbrc
    #
    efgredlemb.p
    @21
    @0
    cQ
    @13
    cP
    ccatswrd
    syl13anc
    oveq1d
    wph
    @168
    @48
    wcel
    #
    @171
    @48
    wcel
    #
    @152
    @178
    @174
    wceq
    wph
    @59
    @184
    @61
    @21
    @0
    cQ
    @13
    swrdcl
    syl
    #
    wph
    @59
    @185
    @61
    @21
    @0
    @13
    cP
    swrdcl
    syl
    #
    @154
    @21
    @168
    @171
    @113
    ccatass
    syl3anc
    wph
    @108
    @117
    @163
    simprd
    3eqtr3d
    wph
    @184
    @172
    @48
    wcel
    #
    @150
    @155
    @168
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    wceq
    @175
    @176
    wb
    @186
    wph
    @185
    @152
    @188
    @187
    @154
    @21
    @171
    @113
    ccatcl
    syl2anc
    @106
    @156
    wph
    @189
    c2
    @190
    wph
    @189
    @13
    cQ
    cmin
    co
    #
    c2
    wph
    @59
    @180
    @66
    @189
    @191
    wceq
    @61
    @182
    @78
    @21
    @0
    cQ
    @13
    swrdlen
    syl3anc
    wph
    cQ
    cc
    wcel
    @88
    @191
    c2
    wceq
    @83
    2cn
    cQ
    c2
    pncan2
    sylancl
    eqtrd
    cV
    @6
    s2len
    syl6eqr
    @168
    @172
    @7
    @115
    @21
    ccatopth
    syl221anc
    mpbid
    #
    simpld
    oveq2d
    wph
    @59
    @129
    @180
    @66
    @169
    @165
    wceq
    @61
    @132
    @182
    @78
    @21
    @0
    cc0
    cQ
    @13
    ccatswrd
    syl13anc
    eqtr3d
    oveq1d
    wph
    @59
    cc0
    @179
    wcel
    #
    @66
    @67
    @166
    @167
    wceq
    @61
    wph
    @68
    @193
    @72
    cc0
    @13
    eluzfz1
    syl
    @78
    @80
    @21
    @0
    cc0
    @13
    @14
    ccatswrd
    syl13anc
    wph
    @59
    @167
    @0
    wceq
    @61
    @21
    @0
    swrdid
    syl
    3eqtrd
    3eqtrd
    wph
    @2
    @19
    @21
    cxp
    #
    wfn
    #
    @20
    @22
    @5
    @3
    wcel
    wph
    @194
    cW
    @2
    wf
    #
    @195
    wph
    @2
    va
    vi
    @19
    @21
    @1
    va
    cv
    #
    @197
    vi
    cv
    #
    @198
    cM
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    wceq
    #
    @196
    wph
    @17
    @199
    @196
    wa
    @28
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
    @1
    va
    vi
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    syl
    simprd
    @194
    cW
    @2
    ffn
    syl
    #
    @101
    efgredlemb.v
    @19
    @21
    cQ
    cV
    @2
    fnovrn
    syl3anc
    eqeltrrd
    wph
    @37
    cU
    @2
    co
    #
    @4
    @3
    wph
    @201
    @1
    @37
    @37
    @111
    cotp
    csplice
    co
    #
    @4
    cc0
    @37
    cop
    csubstr
    co
    #
    @111
    cconcat
    co
    #
    @4
    cP
    @33
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    @4
    wph
    @17
    @37
    @19
    wcel
    #
    @141
    @201
    @202
    wceq
    @28
    wph
    @37
    @29
    wcel
    #
    @39
    @207
    wph
    @40
    @30
    @208
    @100
    @36
    cQ
    @37
    cc0
    uztrn
    syl2anc
    #
    @99
    @37
    cc0
    @18
    elfzuzb
    sylanbrc
    #
    efgredlemb.u
    vy
    vz
    vw
    vv
    cU
    c.sm
    cT
    vn
    cI
    cM
    @37
    cW
    @1
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    wph
    @203
    c0
    @205
    @111
    @1
    @37
    @37
    @21
    wph
    @51
    @203
    @48
    wcel
    #
    @57
    @21
    @4
    cc0
    @37
    swrdcl
    syl
    #
    @104
    wph
    @51
    @205
    @48
    wcel
    #
    @57
    @21
    @4
    cP
    @33
    swrdcl
    syl
    #
    @142
    wph
    @1
    @203
    @205
    cconcat
    co
    #
    @203
    c0
    cconcat
    co
    #
    @205
    cconcat
    co
    wph
    @1
    @43
    @42
    @4
    cQ
    @37
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    @205
    cconcat
    co
    #
    @215
    efgredlemd.sc
    wph
    @43
    @42
    @217
    @205
    cconcat
    co
    #
    cconcat
    co
    #
    @219
    wph
    @15
    @220
    @42
    cconcat
    wph
    @171
    @112
    cconcat
    co
    #
    @15
    @220
    wph
    @59
    @181
    @76
    @67
    @222
    @15
    wceq
    @61
    @183
    efgredlemb.p
    @80
    @21
    @0
    @13
    cP
    @14
    ccatswrd
    syl13anc
    wph
    @171
    @217
    @112
    @205
    cconcat
    wph
    @171
    @217
    wceq
    #
    @113
    @4
    @37
    @33
    cop
    csubstr
    co
    #
    wceq
    #
    wph
    @172
    @217
    @224
    cconcat
    co
    #
    wceq
    #
    @223
    @225
    wa
    #
    wph
    @172
    @115
    @226
    wph
    @170
    @173
    @192
    simprd
    wph
    @51
    cQ
    cc0
    @37
    cfz
    co
    #
    wcel
    #
    @37
    @34
    wcel
    #
    @33
    @34
    wcel
    #
    @226
    @115
    wceq
    @57
    wph
    @30
    @40
    @230
    @36
    @100
    cQ
    cc0
    @37
    elfzuzb
    sylanbrc
    #
    wph
    @208
    @33
    @38
    wcel
    #
    @231
    @209
    wph
    @33
    @73
    wcel
    #
    cP
    @38
    wcel
    #
    @234
    wph
    @14
    @33
    @73
    wph
    vx
    vy
    vz
    vw
    vv
    vt
    cA
    cB
    cD
    cP
    cQ
    c.sm
    cS
    cT
    cU
    vk
    vm
    vn
    cI
    cK
    cL
    cM
    cV
    cW
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgredlem.1
    efgredlem.2
    efgredlem.3
    efgredlem.4
    efgredlem.5
    efgredlemb.k
    efgredlemb.l
    efgredlemb.p
    efgredlemb.q
    efgredlemb.u
    efgredlemb.v
    efgredlemb.6
    efgredlemb.7
    efgredlemg
    @77
    eqeltrrd
    #
    wph
    @90
    @93
    @37
    cP
    cle
    wbr
    #
    @236
    @95
    @94
    wph
    cc0
    c2
    cle
    wbr
    #
    @238
    @239
    wph
    0le2
    a1i
    wph
    cP
    cr
    wcel
    c2
    cr
    wcel
    @239
    @238
    wb
    wph
    cP
    @94
    zred
    2re
    cP
    c2
    subge02
    sylancl
    mpbid
    @37
    cP
    eluz2
    syl3anbrc
    #
    cP
    @33
    @37
    uztrn
    syl2anc
    @37
    cc0
    @33
    elfzuzb
    sylanbrc
    #
    wph
    @33
    @29
    wcel
    @232
    wph
    @33
    cn0
    @29
    wph
    @51
    @33
    cn0
    wcel
    @57
    @21
    @4
    lencl
    syl
    nn0uz
    syl6eleq
    cc0
    @33
    eluzfz2
    syl
    #
    @21
    @4
    cQ
    @37
    @33
    ccatswrd
    syl13anc
    eqtr4d
    wph
    @185
    @152
    @217
    @48
    wcel
    #
    @224
    @48
    wcel
    #
    @171
    chash
    cfv
    #
    @217
    chash
    cfv
    #
    wceq
    @227
    @228
    wb
    @187
    @154
    wph
    @51
    @243
    @57
    @21
    @4
    cQ
    @37
    swrdcl
    syl
    #
    wph
    @51
    @244
    @57
    @21
    @4
    @37
    @33
    swrdcl
    syl
    wph
    @245
    cP
    @13
    cmin
    co
    #
    @246
    wph
    @59
    @181
    @76
    @245
    @248
    wceq
    @61
    @183
    efgredlemb.p
    @21
    @0
    @13
    cP
    swrdlen
    syl3anc
    wph
    @246
    @37
    cQ
    cmin
    co
    #
    cP
    cQ
    cmin
    co
    c2
    cmin
    co
    @248
    wph
    @51
    @230
    @231
    @246
    @249
    wceq
    @57
    @233
    @241
    @21
    @4
    cQ
    @37
    swrdlen
    syl3anc
    wph
    cP
    cQ
    c2
    @98
    @83
    @89
    sub32d
    wph
    cP
    cQ
    c2
    @98
    @83
    @89
    subsub4d
    3eqtr2d
    eqtr4d
    @171
    @113
    @217
    @224
    @21
    ccatopth
    syl221anc
    mpbid
    #
    simpld
    wph
    @111
    @4
    @37
    cP
    cop
    csubstr
    co
    #
    wceq
    #
    @112
    @205
    wceq
    #
    wph
    @113
    @251
    @205
    cconcat
    co
    #
    wceq
    #
    @252
    @253
    wa
    #
    wph
    @113
    @224
    @254
    wph
    @223
    @225
    @250
    simprd
    wph
    @51
    @37
    @130
    wcel
    #
    cP
    @34
    wcel
    #
    @232
    @254
    @224
    wceq
    @57
    wph
    @208
    @236
    @257
    @209
    @240
    @37
    cc0
    cP
    elfzuzb
    sylanbrc
    #
    wph
    cP
    @29
    wcel
    #
    @235
    @258
    wph
    @76
    @260
    efgredlemb.p
    cP
    cc0
    @14
    elfzuz
    syl
    #
    @237
    cP
    cc0
    @33
    elfzuzb
    sylanbrc
    #
    @242
    @21
    @4
    @37
    cP
    @33
    ccatswrd
    syl13anc
    eqtr4d
    wph
    @139
    @140
    @251
    @48
    wcel
    #
    @213
    @111
    chash
    cfv
    #
    @251
    chash
    cfv
    #
    wceq
    @255
    @256
    wb
    @142
    @143
    wph
    @51
    @263
    @57
    @21
    @4
    @37
    cP
    swrdcl
    syl
    @214
    wph
    @264
    c2
    @265
    cU
    @110
    s2len
    wph
    @265
    cP
    @37
    cmin
    co
    #
    c2
    wph
    @51
    @257
    @258
    @265
    @266
    wceq
    @57
    @259
    @262
    @21
    @4
    @37
    cP
    swrdlen
    syl3anc
    wph
    @97
    @88
    @266
    c2
    wceq
    @98
    2cn
    cP
    c2
    nncan
    sylancl
    eqtr2d
    syl5eq
    @111
    @112
    @251
    @205
    @21
    ccatopth
    syl221anc
    mpbid
    #
    simprd
    oveq12d
    eqtr3d
    oveq2d
    wph
    @49
    @243
    @213
    @219
    @221
    wceq
    @58
    @247
    @214
    @21
    @42
    @217
    @205
    ccatass
    syl3anc
    eqtr4d
    wph
    @218
    @203
    @205
    cconcat
    wph
    @51
    @129
    @230
    @231
    @218
    @203
    wceq
    @57
    @132
    @233
    @241
    @21
    @4
    cc0
    cQ
    @37
    ccatswrd
    syl13anc
    oveq1d
    3eqtrd
    wph
    @216
    @203
    @205
    cconcat
    wph
    @211
    @216
    @203
    wceq
    @212
    @21
    @203
    ccatrid
    syl
    oveq1d
    eqtr4d
    wph
    @203
    chash
    cfv
    #
    @37
    wph
    @51
    @231
    @268
    @37
    wceq
    @57
    @241
    @21
    @4
    @37
    swrd0len
    syl2anc
    eqcomd
    wph
    @37
    @164
    caddc
    co
    @37
    cc0
    caddc
    co
    @37
    @164
    cc0
    @37
    caddc
    hash0
    oveq2i
    wph
    @37
    wph
    @37
    @95
    zcnd
    addid1d
    syl5req
    splval2
    wph
    @206
    @4
    @125
    csubstr
    co
    #
    @205
    cconcat
    co
    #
    @4
    cc0
    @33
    cop
    csubstr
    co
    #
    @4
    wph
    @204
    @269
    @205
    cconcat
    wph
    @204
    @203
    @251
    cconcat
    co
    #
    @269
    wph
    @111
    @251
    @203
    cconcat
    wph
    @252
    @253
    @267
    simpld
    oveq2d
    wph
    @51
    cc0
    @229
    wcel
    #
    @257
    @258
    @272
    @269
    wceq
    @57
    wph
    @208
    @273
    @209
    cc0
    @37
    eluzfz1
    syl
    @259
    @262
    @21
    @4
    cc0
    @37
    cP
    ccatswrd
    syl13anc
    eqtrd
    oveq1d
    wph
    @51
    cc0
    @130
    wcel
    #
    @258
    @232
    @270
    @271
    wceq
    @57
    wph
    @260
    @274
    @261
    cc0
    cP
    eluzfz1
    syl
    @262
    @242
    @21
    @4
    cc0
    cP
    @33
    ccatswrd
    syl13anc
    wph
    @51
    @271
    @4
    wceq
    @57
    @21
    @4
    swrdid
    syl
    3eqtrd
    3eqtrd
    wph
    @195
    @207
    @141
    @201
    @3
    wcel
    @200
    @210
    efgredlemb.u
    @19
    @21
    @37
    cU
    @2
    fnovrn
    syl3anc
    eqeltrrd
    jca
end
