include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wo.mm"
include "cc0.mm"
include "uzp1.mm"
include "cop.mm"
include "csubstr.mm"
include "chash.mm"
include "cconcat.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cfz.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "cfzo.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cdm.mm"
include "cv.mm"
include "cmin.mm"
include "crn.mm"
include "wral.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "syl.mm"
include "eldifi.mm"
include "wrdf.mm"
include "3syl.mm"
include "fzossfz.mm"
include "cn.mm"
include "efgredlema.mm"
include "simpld.mm"
include "fzo0end.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "cz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "elfzuz.mm"
include "eluzfz1.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "swrdid.mm"
include "eqtrd.mm"
include "simprd.mm"
include "eqeq12d.mm"
include "mtbird.mm"
include "wa.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "efgtval.mm"
include "syl3anc.mm"
include "efgmf.mm"
include "ffvelrni.mm"
include "s2cld.mm"
include "splval.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"
include "adantr.mm"
include "wb.mm"
include "swrdcl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "swrd0len.mm"
include "biimpar.mm"
include "c2.mm"
include "s2len.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "ccatlen.mm"
include "3eqtr4d.mm"
include "ccatopth.mm"
include "syl221anc.mm"
include "mpbid.mm"
include "mtand.mm"
include "pm2.21d.mm"
include "cs1.mm"
include "s1cld.mm"
include "ccatass.mm"
include "df-s2.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "s1len.mm"
include "s111.mm"
include "fveq2d.mm"
include "efgmnvl.mm"
include "s1eqd.mm"
include "oveq2d.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "1cnd.mm"
include "addassd.mm"
include "df-2.mm"
include "eleq2d.mm"
include "wrex.mm"
include "wfo.mm"
include "efgsfo.mm"
include "cvv.mm"
include "efgrcl.mm"
include "foelrn.mm"
include "sylancr.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "ad2antrr.mm"
include "wn.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "eqcomd.mm"
include "efgredlemd.mm"
include "rexlimddv.mm"
include "ex.mm"
include "sylbid.mm"
include "jaod.mm"
include "syl5.mm"

theorem efgredlemc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
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
  let cC: class C
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
  disjoint L c
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
  assert |- ( ph -> ( P e. ( ZZ>= ` Q ) -> ( A ` 0 ) = ( B ` 0 ) ) )

  proof
    cP
    cQ
    cuz
    cfv
    wcel
    cP
    cQ
    wceq
    #
    cP
    cQ
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wo
    wph
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
    cQ
    cP
    uzp1
    wph
    @0
    @5
    @2
    wph
    @0
    @5
    wph
    @0
    cK
    cA
    cfv
    #
    cc0
    cP
    cop
    csubstr
    co
    #
    @6
    cP
    @6
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
    cL
    cB
    cfv
    #
    cc0
    cQ
    cop
    csubstr
    co
    #
    @11
    cQ
    @11
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
    wceq
    #
    wph
    @16
    @6
    @11
    wceq
    #
    efgredlemb.8
    wph
    @10
    @6
    @15
    @11
    wph
    @10
    @6
    cc0
    @8
    cop
    csubstr
    co
    #
    @6
    wph
    @6
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    #
    cc0
    cc0
    cP
    cfz
    co
    wcel
    #
    cP
    cc0
    @8
    cfz
    co
    #
    wcel
    #
    @8
    @23
    wcel
    #
    @10
    @18
    wceq
    wph
    cW
    @20
    @6
    cW
    @20
    cid
    cfv
    @20
    efgval.w
    @20
    fviss
    eqsstri
    #
    wph
    cc0
    cA
    chash
    cfv
    #
    cfzo
    co
    #
    cW
    cK
    cA
    wph
    cA
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
    cA
    @29
    wcel
    #
    @28
    cW
    cA
    wf
    wph
    cA
    cS
    cdm
    #
    wcel
    #
    @32
    efgredlem.2
    @35
    @32
    @3
    cD
    wcel
    vi
    cv
    #
    cA
    cfv
    @36
    c1
    cmin
    co
    #
    cA
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @27
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
    cA
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
    syl
    #
    cA
    @29
    @30
    eldifi
    #
    cW
    cA
    wrdf
    3syl
    wph
    cK
    cc0
    @27
    c1
    cmin
    co
    #
    cfz
    co
    #
    @28
    wph
    cc0
    @40
    cfzo
    co
    #
    @41
    cK
    cc0
    @40
    fzossfz
    wph
    cK
    @40
    c1
    cmin
    co
    #
    @42
    efgredlemb.k
    wph
    @40
    cn
    wcel
    #
    @43
    @42
    wcel
    wph
    @44
    cB
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cn
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
    efgredlema
    #
    simpld
    @40
    fzo0end
    syl
    syl5eqel
    sseldi
    wph
    @27
    cz
    wcel
    @28
    @41
    wceq
    wph
    @27
    wph
    @32
    @33
    @27
    cn0
    wcel
    @38
    @39
    cW
    cA
    lencl
    3syl
    nn0zd
    cc0
    @27
    fzoval
    syl
    eleqtrrd
    ffvelrnd
    #
    sseldi
    #
    wph
    @24
    cP
    cc0
    cuz
    cfv
    #
    wcel
    @22
    efgredlemb.p
    cP
    cc0
    @8
    elfzuz
    cc0
    cP
    eluzfz1
    3syl
    efgredlemb.p
    wph
    @8
    @51
    wcel
    @25
    wph
    @8
    cn0
    @51
    wph
    @21
    @8
    cn0
    wcel
    @50
    @19
    @6
    lencl
    syl
    nn0uz
    syl6eleq
    cc0
    @8
    eluzfz2
    syl
    @19
    @6
    cc0
    cP
    @8
    ccatswrd
    syl13anc
    wph
    @21
    @18
    @6
    wceq
    @50
    @19
    @6
    swrdid
    syl
    eqtrd
    wph
    @15
    @11
    cc0
    @13
    cop
    csubstr
    co
    #
    @11
    wph
    @11
    @20
    wcel
    #
    cc0
    cc0
    cQ
    cfz
    co
    wcel
    #
    cQ
    cc0
    @13
    cfz
    co
    #
    wcel
    #
    @13
    @55
    wcel
    #
    @15
    @52
    wceq
    wph
    cW
    @20
    @11
    @26
    wph
    cc0
    @45
    cfzo
    co
    #
    cW
    cL
    cB
    wph
    cB
    @31
    wcel
    #
    cB
    @29
    wcel
    #
    @58
    cW
    cB
    wf
    wph
    cB
    @34
    wcel
    #
    @59
    efgredlem.3
    @61
    @59
    @4
    cD
    wcel
    @36
    cB
    cfv
    @37
    cB
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @45
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
    cB
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
    syl
    #
    cB
    @29
    @30
    eldifi
    #
    cW
    cB
    wrdf
    3syl
    wph
    cL
    cc0
    @46
    cfz
    co
    #
    @58
    wph
    cc0
    @46
    cfzo
    co
    #
    @64
    cL
    cc0
    @46
    fzossfz
    wph
    cL
    @46
    c1
    cmin
    co
    #
    @65
    efgredlemb.l
    wph
    @47
    @66
    @65
    wcel
    wph
    @44
    @47
    @48
    simprd
    @46
    fzo0end
    syl
    syl5eqel
    sseldi
    wph
    @45
    cz
    wcel
    @58
    @64
    wceq
    wph
    @45
    wph
    @59
    @60
    @45
    cn0
    wcel
    @62
    @63
    cW
    cB
    lencl
    3syl
    nn0zd
    cc0
    @45
    fzoval
    syl
    eleqtrrd
    ffvelrnd
    #
    sseldi
    #
    wph
    @56
    cQ
    @51
    wcel
    @54
    efgredlemb.q
    cQ
    cc0
    @13
    elfzuz
    cc0
    cQ
    eluzfz1
    3syl
    efgredlemb.q
    wph
    @13
    @51
    wcel
    @57
    wph
    @13
    cn0
    @51
    wph
    @53
    @13
    cn0
    wcel
    @68
    @19
    @11
    lencl
    syl
    nn0uz
    syl6eleq
    cc0
    @13
    eluzfz2
    syl
    @19
    @11
    cc0
    cQ
    @13
    ccatswrd
    syl13anc
    wph
    @53
    @52
    @11
    wceq
    @68
    @19
    @11
    swrdid
    syl
    eqtrd
    eqeq12d
    mtbird
    #
    wph
    @0
    wa
    #
    @7
    @12
    @9
    @14
    cconcat
    @70
    @7
    @12
    wceq
    #
    cU
    cU
    cM
    cfv
    #
    cs2
    #
    cV
    cV
    cM
    cfv
    #
    cs2
    #
    wceq
    #
    @70
    @7
    @73
    cconcat
    co
    #
    @12
    @75
    cconcat
    co
    #
    wceq
    #
    @71
    @76
    wa
    #
    @70
    @79
    @9
    @14
    wceq
    #
    @70
    @77
    @9
    cconcat
    co
    #
    @78
    @14
    cconcat
    co
    #
    wceq
    #
    @79
    @81
    wa
    #
    wph
    @84
    @0
    wph
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    @82
    @83
    efgredlem.4
    wph
    @86
    cP
    cU
    @6
    cT
    cfv
    co
    #
    @6
    cP
    cP
    @73
    cotp
    csplice
    co
    #
    @82
    efgredlemb.6
    wph
    @6
    cW
    wcel
    #
    @24
    cU
    @19
    wcel
    #
    @88
    @89
    wceq
    @49
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
    @6
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    wph
    @90
    @24
    @24
    @73
    @20
    wcel
    #
    @89
    @82
    wceq
    @49
    efgredlemb.p
    efgredlemb.p
    wph
    cU
    @72
    @19
    efgredlemb.u
    wph
    @91
    @72
    @19
    wcel
    efgredlemb.u
    @19
    @19
    cU
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
    #
    s2cld
    #
    @73
    @6
    cP
    cP
    cW
    @23
    @23
    @20
    splval
    syl13anc
    3eqtrd
    wph
    @87
    cQ
    cV
    @11
    cT
    cfv
    co
    #
    @11
    cQ
    cQ
    @75
    cotp
    csplice
    co
    #
    @83
    efgredlemb.7
    wph
    @11
    cW
    wcel
    #
    @56
    cV
    @19
    wcel
    #
    @96
    @97
    wceq
    @67
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
    @11
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    wph
    @98
    @56
    @56
    @75
    @20
    wcel
    #
    @97
    @83
    wceq
    @67
    efgredlemb.q
    efgredlemb.q
    wph
    cV
    @74
    @19
    efgredlemb.v
    wph
    @99
    @74
    @19
    wcel
    #
    efgredlemb.v
    @19
    @19
    cV
    cM
    @93
    ffvelrni
    syl
    #
    s2cld
    #
    @75
    @11
    cQ
    cQ
    cW
    @55
    @55
    @20
    splval
    syl13anc
    3eqtrd
    3eqtr3d
    #
    adantr
    @70
    @77
    @20
    wcel
    #
    @9
    @20
    wcel
    #
    @78
    @20
    wcel
    #
    @14
    @20
    wcel
    #
    @77
    chash
    cfv
    #
    @78
    chash
    cfv
    #
    wceq
    @84
    @85
    wb
    @70
    @7
    @20
    wcel
    #
    @92
    @105
    wph
    @111
    @0
    wph
    @21
    @111
    @50
    @19
    @6
    cc0
    cP
    swrdcl
    syl
    #
    adantr
    #
    wph
    @92
    @0
    @95
    adantr
    #
    @19
    @7
    @73
    ccatcl
    syl2anc
    wph
    @106
    @0
    wph
    @21
    @106
    @50
    @19
    @6
    cP
    @8
    swrdcl
    syl
    #
    adantr
    @70
    @12
    @20
    wcel
    #
    @100
    @107
    wph
    @116
    @0
    wph
    @53
    @116
    @68
    @19
    @11
    cc0
    cQ
    swrdcl
    syl
    #
    adantr
    #
    wph
    @100
    @0
    @103
    adantr
    #
    @19
    @12
    @75
    ccatcl
    syl2anc
    wph
    @108
    @0
    wph
    @53
    @108
    @68
    @19
    @11
    cQ
    @13
    swrdcl
    syl
    #
    adantr
    @70
    @7
    chash
    cfv
    #
    @73
    chash
    cfv
    #
    caddc
    co
    #
    @12
    chash
    cfv
    #
    @75
    chash
    cfv
    #
    caddc
    co
    #
    @109
    @110
    @70
    @121
    @124
    @122
    @125
    caddc
    wph
    @121
    @124
    wceq
    #
    @0
    wph
    @121
    cP
    @124
    cQ
    wph
    @21
    @24
    @121
    cP
    wceq
    @50
    efgredlemb.p
    @19
    @6
    cP
    swrd0len
    syl2anc
    #
    wph
    @53
    @56
    @124
    cQ
    wceq
    @68
    efgredlemb.q
    @19
    @11
    cQ
    swrd0len
    syl2anc
    #
    eqeq12d
    biimpar
    #
    @122
    @125
    wceq
    @70
    @122
    c2
    @125
    cU
    @72
    s2len
    cV
    @74
    s2len
    eqtr4i
    a1i
    oveq12d
    @70
    @111
    @92
    @109
    @123
    wceq
    @113
    @114
    @19
    @7
    @73
    ccatlen
    syl2anc
    @70
    @116
    @100
    @110
    @126
    wceq
    @118
    @119
    @19
    @12
    @75
    ccatlen
    syl2anc
    3eqtr4d
    @77
    @9
    @78
    @14
    @19
    ccatopth
    syl221anc
    mpbid
    #
    simpld
    @70
    @111
    @92
    @116
    @100
    @127
    @79
    @80
    wb
    @113
    @114
    @118
    @119
    @130
    @7
    @73
    @12
    @75
    @19
    ccatopth
    syl221anc
    mpbid
    simpld
    @70
    @79
    @81
    @131
    simprd
    oveq12d
    mtand
    pm2.21d
    @2
    cP
    @1
    wceq
    #
    cP
    @1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wo
    wph
    @5
    @1
    cP
    uzp1
    wph
    @132
    @5
    @135
    wph
    @132
    @5
    wph
    @132
    @16
    @69
    wph
    @132
    wa
    #
    @10
    @12
    cV
    cs1
    #
    cconcat
    co
    #
    @9
    cconcat
    co
    #
    @12
    @137
    @9
    cconcat
    co
    #
    cconcat
    co
    #
    @15
    @136
    @7
    @138
    @9
    cconcat
    @136
    @7
    @138
    wceq
    #
    cU
    cs1
    #
    @74
    cs1
    #
    wceq
    #
    @136
    @7
    @143
    cconcat
    co
    #
    @138
    @144
    cconcat
    co
    #
    wceq
    #
    @142
    @145
    wa
    #
    @136
    @148
    @72
    cs1
    #
    @9
    cconcat
    co
    #
    @14
    wceq
    #
    @136
    @146
    @151
    cconcat
    co
    #
    @147
    @14
    cconcat
    co
    #
    wceq
    #
    @148
    @152
    wa
    #
    wph
    @155
    @132
    wph
    @146
    @150
    cconcat
    co
    #
    @9
    cconcat
    co
    #
    @153
    @154
    wph
    @146
    @20
    wcel
    #
    @150
    @20
    wcel
    #
    @106
    @158
    @153
    wceq
    wph
    @111
    @143
    @20
    wcel
    #
    @159
    @112
    wph
    cU
    @19
    efgredlemb.u
    s1cld
    #
    @19
    @7
    @143
    ccatcl
    syl2anc
    #
    wph
    @72
    @19
    @94
    s1cld
    #
    @115
    @19
    @146
    @150
    @9
    ccatass
    syl3anc
    wph
    @82
    @83
    @158
    @154
    @104
    wph
    @157
    @77
    @9
    cconcat
    wph
    @157
    @7
    @143
    @150
    cconcat
    co
    #
    cconcat
    co
    #
    @77
    wph
    @111
    @161
    @160
    @157
    @166
    wceq
    @112
    @162
    @164
    @19
    @7
    @143
    @150
    ccatass
    syl3anc
    @73
    @165
    @7
    cconcat
    cU
    @72
    df-s2
    oveq2i
    syl6eqr
    oveq1d
    wph
    @147
    @78
    @14
    cconcat
    wph
    @147
    @12
    @137
    @144
    cconcat
    co
    #
    cconcat
    co
    #
    @78
    wph
    @116
    @137
    @20
    wcel
    #
    @144
    @20
    wcel
    #
    @147
    @168
    wceq
    @117
    wph
    cV
    @19
    efgredlemb.v
    s1cld
    #
    wph
    @74
    @19
    @102
    s1cld
    #
    @19
    @12
    @137
    @144
    ccatass
    syl3anc
    @75
    @167
    @12
    cconcat
    cV
    @74
    df-s2
    oveq2i
    syl6eqr
    oveq1d
    3eqtr4d
    eqtr3d
    adantr
    @136
    @159
    @151
    @20
    wcel
    #
    @147
    @20
    wcel
    #
    @108
    @146
    chash
    cfv
    #
    @147
    chash
    cfv
    #
    wceq
    @155
    @156
    wb
    wph
    @159
    @132
    @163
    adantr
    @136
    @160
    @106
    @173
    wph
    @160
    @132
    @164
    adantr
    wph
    @106
    @132
    @115
    adantr
    #
    @19
    @150
    @9
    ccatcl
    syl2anc
    @136
    @138
    @20
    wcel
    #
    @170
    @174
    wph
    @178
    @132
    wph
    @116
    @169
    @178
    @117
    @171
    @19
    @12
    @137
    ccatcl
    syl2anc
    adantr
    #
    wph
    @170
    @132
    @172
    adantr
    #
    @19
    @138
    @144
    ccatcl
    syl2anc
    wph
    @108
    @132
    @120
    adantr
    @136
    @121
    @143
    chash
    cfv
    #
    caddc
    co
    #
    @138
    chash
    cfv
    #
    @144
    chash
    cfv
    #
    caddc
    co
    #
    @175
    @176
    @136
    @121
    @183
    @181
    @184
    caddc
    wph
    @121
    @183
    wceq
    #
    @132
    wph
    @121
    cP
    @183
    @1
    @128
    wph
    @183
    @124
    @137
    chash
    cfv
    #
    caddc
    co
    #
    @1
    wph
    @116
    @169
    @183
    @188
    wceq
    @117
    @171
    @19
    @12
    @137
    ccatlen
    syl2anc
    wph
    @124
    cQ
    @187
    c1
    caddc
    @129
    @187
    c1
    wceq
    wph
    cV
    s1len
    a1i
    oveq12d
    eqtrd
    eqeq12d
    biimpar
    #
    @181
    @184
    wceq
    @136
    @181
    c1
    @184
    cU
    s1len
    @74
    s1len
    eqtr4i
    a1i
    oveq12d
    @136
    @111
    @161
    @175
    @182
    wceq
    wph
    @111
    @132
    @112
    adantr
    #
    wph
    @161
    @132
    @162
    adantr
    #
    @19
    @7
    @143
    ccatlen
    syl2anc
    @136
    @178
    @170
    @176
    @185
    wceq
    @179
    @180
    @19
    @138
    @144
    ccatlen
    syl2anc
    3eqtr4d
    @146
    @151
    @147
    @14
    @19
    ccatopth
    syl221anc
    mpbid
    #
    simpld
    @136
    @111
    @161
    @178
    @170
    @186
    @148
    @149
    wb
    @190
    @191
    @179
    @180
    @189
    @7
    @143
    @138
    @144
    @19
    ccatopth
    syl221anc
    mpbid
    #
    simpld
    oveq1d
    @136
    @116
    @169
    @106
    @139
    @141
    wceq
    wph
    @116
    @132
    @117
    adantr
    wph
    @169
    @132
    @171
    adantr
    @177
    @19
    @12
    @137
    @9
    ccatass
    syl3anc
    @136
    @140
    @14
    @12
    cconcat
    @136
    @151
    @140
    @14
    @136
    @150
    @137
    @9
    cconcat
    @136
    @72
    cV
    @136
    @72
    @74
    cM
    cfv
    #
    cV
    @136
    cU
    @74
    cM
    @136
    @145
    cU
    @74
    wceq
    #
    @136
    @142
    @145
    @193
    simprd
    wph
    @145
    @195
    wb
    #
    @132
    wph
    @91
    @101
    @196
    efgredlemb.u
    @102
    @19
    cU
    @74
    s111
    syl2anc
    adantr
    mpbid
    fveq2d
    wph
    @194
    cV
    wceq
    #
    @132
    wph
    @99
    @197
    efgredlemb.v
    vy
    vz
    cV
    cI
    cM
    efgval2.m
    efgmnvl
    syl
    adantr
    eqtrd
    s1eqd
    oveq1d
    @136
    @148
    @152
    @192
    simprd
    eqtr3d
    oveq2d
    3eqtrd
    mtand
    pm2.21d
    wph
    @135
    cP
    cQ
    c2
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @5
    wph
    @134
    @199
    cP
    wph
    @133
    @198
    cuz
    wph
    @133
    cQ
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @198
    wph
    cQ
    c1
    c1
    wph
    cQ
    wph
    @56
    cQ
    cz
    wcel
    efgredlemb.q
    cQ
    cc0
    @13
    elfzelz
    syl
    zcnd
    wph
    1cnd
    #
    @202
    addassd
    c2
    @201
    cQ
    caddc
    df-2
    oveq2i
    syl6eqr
    fveq2d
    eleq2d
    wph
    @200
    @5
    wph
    @200
    wa
    #
    @12
    @6
    @198
    @8
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    vc
    cv
    #
    cS
    cfv
    #
    wceq
    #
    @5
    vc
    @34
    wph
    @208
    vc
    @34
    wrex
    #
    @200
    wph
    @34
    cW
    cS
    wfo
    @205
    cW
    wcel
    @209
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
    efgsfo
    wph
    @205
    @20
    cW
    wph
    @116
    @204
    @20
    wcel
    #
    @205
    @20
    wcel
    @117
    wph
    @21
    @210
    @50
    @19
    @6
    @198
    @8
    swrdcl
    syl
    @19
    @12
    @204
    ccatcl
    syl2anc
    wph
    cI
    cvv
    wcel
    #
    cW
    @20
    wceq
    #
    wph
    @90
    @211
    @212
    wa
    @49
    @6
    cI
    cW
    efgval.w
    efgrcl
    syl
    simprd
    eleqtrrd
    vc
    @34
    cW
    @205
    cS
    foelrn
    sylancr
    adantr
    @203
    @206
    @34
    wcel
    #
    @208
    wa
    #
    wa
    #
    vx
    vy
    vz
    vw
    vv
    vt
    cA
    cB
    @206
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
    wph
    va
    cv
    #
    cS
    cfv
    #
    chash
    cfv
    @86
    chash
    cfv
    clt
    wbr
    @217
    vb
    cv
    #
    cS
    cfv
    wceq
    cc0
    @216
    cfv
    cc0
    @218
    cfv
    wceq
    wi
    wi
    vb
    @34
    wral
    va
    @34
    wral
    @200
    @214
    efgredlem.1
    ad2antrr
    wph
    @35
    @200
    @214
    efgredlem.2
    ad2antrr
    wph
    @61
    @200
    @214
    efgredlem.3
    ad2antrr
    wph
    @86
    @87
    wceq
    @200
    @214
    efgredlem.4
    ad2antrr
    wph
    @5
    wn
    @200
    @214
    efgredlem.5
    ad2antrr
    efgredlemb.k
    efgredlemb.l
    wph
    @24
    @200
    @214
    efgredlemb.p
    ad2antrr
    wph
    @56
    @200
    @214
    efgredlemb.q
    ad2antrr
    wph
    @91
    @200
    @214
    efgredlemb.u
    ad2antrr
    wph
    @99
    @200
    @214
    efgredlemb.v
    ad2antrr
    wph
    @86
    @88
    wceq
    @200
    @214
    efgredlemb.6
    ad2antrr
    wph
    @87
    @96
    wceq
    @200
    @214
    efgredlemb.7
    ad2antrr
    wph
    @17
    wn
    @200
    @214
    efgredlemb.8
    ad2antrr
    wph
    @200
    @214
    simplr
    @203
    @213
    @208
    simprl
    @215
    @205
    @207
    @203
    @213
    @208
    simprr
    eqcomd
    efgredlemd
    rexlimddv
    ex
    sylbid
    jaod
    syl5
    jaod
    syl5
end
