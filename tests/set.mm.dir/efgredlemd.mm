include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "cres.mm"
include "cs1.mm"
include "cconcat.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cdm.mm"
include "cdif.mm"
include "cv.mm"
include "crn.mm"
include "wral.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "syl.mm"
include "eldifad.mm"
include "wf.mm"
include "wrdf.mm"
include "cfz.mm"
include "fzossfz.mm"
include "cz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "syl5sseqr.mm"
include "cn.mm"
include "efgredlema.mm"
include "simpld.mm"
include "fzo0end.mm"
include "syl5eqel.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "s1cld.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "lennncl.mm"
include "sylbi.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "simprd.mm"
include "eqtr4d.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "caddc.mm"
include "cr.mm"
include "crp.mm"
include "c2o.mm"
include "cxp.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "nn0red.mm"
include "2rp.mm"
include "ltaddrp.mm"
include "sylancl.mm"
include "cle.mm"
include "lem1d.mm"
include "wb.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "efgsres.mm"
include "syl2anc.mm"
include "efgsval.mm"
include "cop.mm"
include "csubstr.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "swrd0val.mm"
include "fveq2d.mm"
include "swrd0len.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "syl6eqr.mm"
include "fvres.mm"
include "3eqtrd.mm"
include "efgsdmi.mm"
include "fveq2i.mm"
include "rneqi.mm"
include "syl6eleqr.mm"
include "efgtlen.mm"
include "3brtr4d.mm"
include "efgredleme.mm"
include "efgsp1.mm"
include "efgsval2.mm"
include "wi.mm"
include "fveq2.mm"
include "breq1d.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "mp2d.mm"
include "eqeltrd.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"

theorem efgredlemd
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
  assert |- ( ph -> ( A ` 0 ) = ( B ` 0 ) )

  proof
    wph
    cc0
    cA
    cc0
    cA
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cres
    #
    cfv
    #
    cc0
    cB
    cc0
    cB
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cres
    #
    cfv
    #
    cc0
    cA
    cfv
    #
    cc0
    cB
    cfv
    #
    wph
    cc0
    cC
    cK
    cA
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cfv
    #
    cc0
    cC
    cL
    cB
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cfv
    #
    @4
    @9
    wph
    @15
    cc0
    cC
    cfv
    #
    @19
    wph
    cC
    cW
    cword
    #
    wcel
    #
    @13
    @21
    wcel
    cc0
    cc0
    cC
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    @15
    @20
    wceq
    wph
    cC
    @21
    c0
    csn
    #
    wph
    cC
    cS
    cdm
    #
    wcel
    #
    cC
    @21
    @25
    cdif
    #
    wcel
    #
    efgredlemd.c
    @27
    @29
    @20
    cD
    wcel
    vi
    cv
    #
    cC
    cfv
    @30
    c1
    cmin
    co
    #
    cC
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @23
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
    cC
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
    eldifad
    #
    wph
    @12
    cW
    wph
    cc0
    @0
    cfzo
    co
    #
    cW
    cK
    cA
    wph
    cA
    @21
    wcel
    #
    @34
    cW
    cA
    wf
    wph
    cA
    @21
    @25
    wph
    cA
    @26
    wcel
    #
    cA
    @28
    wcel
    #
    efgredlem.2
    @36
    @37
    @10
    cD
    wcel
    @30
    cA
    cfv
    @31
    cA
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @0
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
    eldifad
    #
    cW
    cA
    wrdf
    syl
    wph
    @2
    @34
    cK
    wph
    cc0
    @1
    cfz
    co
    #
    @2
    @34
    cc0
    @1
    fzossfz
    wph
    @0
    cz
    wcel
    #
    @34
    @39
    wceq
    wph
    @0
    wph
    @35
    @0
    cn0
    wcel
    @38
    cW
    cA
    lencl
    syl
    #
    nn0zd
    #
    cc0
    @0
    fzoval
    syl
    syl5sseqr
    wph
    cK
    @1
    c1
    cmin
    co
    #
    @2
    efgredlemb.k
    wph
    @1
    cn
    wcel
    #
    @43
    @2
    wcel
    wph
    @44
    @6
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
    #
    @1
    fzo0end
    syl
    syl5eqel
    #
    sseldd
    ffvelrnd
    #
    s1cld
    wph
    @23
    cn
    wcel
    #
    @24
    wph
    @29
    @50
    @32
    @29
    @22
    cC
    c0
    wne
    wa
    @50
    cC
    @21
    c0
    eldifsn
    cW
    cC
    lennncl
    sylbi
    syl
    @23
    lbfzo0
    sylibr
    #
    cW
    cC
    @13
    cc0
    ccatval1
    syl3anc
    wph
    @22
    @17
    @21
    wcel
    @24
    @19
    @20
    wceq
    @33
    wph
    @16
    cW
    wph
    cc0
    @5
    cfzo
    co
    #
    cW
    cL
    cB
    wph
    cB
    @21
    wcel
    #
    @52
    cW
    cB
    wf
    wph
    cB
    @21
    @25
    wph
    cB
    @26
    wcel
    #
    cB
    @28
    wcel
    #
    efgredlem.3
    @54
    @55
    @11
    cD
    wcel
    @30
    cB
    cfv
    @31
    cB
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @5
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
    eldifad
    #
    cW
    cB
    wrdf
    syl
    wph
    @7
    @52
    cL
    wph
    cc0
    @6
    cfz
    co
    #
    @7
    @52
    cc0
    @6
    fzossfz
    wph
    @5
    cz
    wcel
    #
    @52
    @57
    wceq
    wph
    @5
    wph
    @53
    @5
    cn0
    wcel
    @56
    cW
    cB
    lencl
    syl
    #
    nn0zd
    #
    cc0
    @5
    fzoval
    syl
    syl5sseqr
    wph
    cL
    @6
    c1
    cmin
    co
    #
    @7
    efgredlemb.l
    wph
    @45
    @61
    @7
    wcel
    wph
    @44
    @45
    @46
    simprd
    #
    @6
    fzo0end
    syl
    syl5eqel
    #
    sseldd
    ffvelrnd
    #
    s1cld
    @51
    cW
    cC
    @17
    cc0
    ccatval1
    syl3anc
    eqtr4d
    wph
    @3
    cS
    cfv
    #
    chash
    cfv
    #
    cA
    cS
    cfv
    #
    chash
    cfv
    #
    clt
    wbr
    #
    @65
    @14
    cS
    cfv
    #
    wceq
    #
    @4
    @15
    wceq
    #
    wph
    @12
    chash
    cfv
    #
    @73
    c2
    caddc
    co
    #
    @66
    @68
    clt
    wph
    @73
    cr
    wcel
    c2
    crp
    wcel
    #
    @73
    @74
    clt
    wbr
    wph
    @73
    wph
    @12
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    @73
    cn0
    wcel
    wph
    cW
    @77
    @12
    cW
    @77
    cid
    cfv
    @77
    efgval.w
    @77
    fviss
    eqsstri
    #
    @49
    sseldi
    @76
    @12
    lencl
    syl
    nn0red
    2rp
    @73
    c2
    ltaddrp
    sylancl
    wph
    @65
    @12
    chash
    wph
    @65
    @3
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @3
    cfv
    #
    cK
    @3
    cfv
    #
    @12
    wph
    @3
    @26
    wcel
    #
    @65
    @81
    wceq
    wph
    @36
    @1
    c1
    @0
    cfz
    co
    #
    wcel
    #
    @83
    efgredlem.2
    wph
    @85
    @44
    @1
    @0
    cle
    wbr
    #
    @47
    wph
    @0
    wph
    @0
    @41
    nn0red
    lem1d
    wph
    @40
    @85
    @44
    @86
    wa
    wb
    @42
    @1
    @0
    fznn
    syl
    mpbir2and
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
    cA
    cI
    cM
    @1
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsres
    syl2anc
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
    @3
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
    wph
    @80
    cK
    @3
    wph
    @80
    @43
    cK
    wph
    @79
    @1
    c1
    cmin
    wph
    cA
    cc0
    @1
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    @79
    @1
    wph
    @89
    @3
    chash
    wph
    @35
    @1
    cc0
    @0
    cfz
    co
    #
    wcel
    #
    @89
    @3
    wceq
    @38
    wph
    @84
    @91
    @1
    c1
    cc0
    cuz
    cfv
    wcel
    #
    @84
    @91
    wss
    1eluzge0
    c1
    cc0
    @0
    fzss1
    ax-mp
    @87
    sseldi
    #
    cW
    cA
    @1
    swrd0val
    syl2anc
    fveq2d
    wph
    @35
    @92
    @90
    @1
    wceq
    @38
    @94
    cW
    cA
    @1
    swrd0len
    syl2anc
    eqtr3d
    oveq1d
    efgredlemb.k
    syl6eqr
    fveq2d
    wph
    cK
    @2
    wcel
    @82
    @12
    wceq
    @48
    cK
    @2
    cA
    fvres
    syl
    3eqtrd
    #
    fveq2d
    wph
    @12
    cW
    wcel
    #
    @67
    @12
    cT
    cfv
    #
    crn
    #
    wcel
    @68
    @74
    wceq
    @49
    wph
    @67
    @43
    cA
    cfv
    #
    cT
    cfv
    #
    crn
    #
    @98
    wph
    @36
    @44
    @67
    @101
    wcel
    efgredlem.2
    @47
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
    efgsdmi
    syl2anc
    @97
    @100
    @12
    @99
    cT
    cK
    @43
    cA
    efgredlemb.k
    fveq2i
    fveq2i
    rneqi
    syl6eleqr
    vy
    vz
    vw
    vv
    @67
    c.sm
    cT
    vn
    cI
    cM
    cW
    @12
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtlen
    syl2anc
    3brtr4d
    wph
    @65
    @12
    @70
    @95
    wph
    @22
    @96
    @14
    @26
    wcel
    #
    @70
    @12
    wceq
    @33
    @49
    wph
    @27
    @12
    cC
    cS
    cfv
    cT
    cfv
    crn
    #
    wcel
    #
    @102
    efgredlemd.c
    wph
    @104
    @16
    @103
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
    cC
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
    efgredlemb.8
    efgredlemd.9
    efgredlemd.c
    efgredlemd.sc
    efgredleme
    #
    simpld
    vx
    vy
    vz
    vw
    vv
    vt
    @12
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cC
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
    cC
    @12
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
    eqtr4d
    wph
    @83
    @102
    va
    cv
    #
    cS
    cfv
    #
    chash
    cfv
    #
    @68
    clt
    wbr
    #
    @109
    vb
    cv
    #
    cS
    cfv
    #
    wceq
    #
    cc0
    @108
    cfv
    #
    cc0
    @112
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    vb
    @26
    wral
    va
    @26
    wral
    #
    @69
    @71
    @72
    wi
    #
    wi
    #
    @88
    @107
    efgredlem.1
    @119
    @122
    @69
    @65
    @113
    wceq
    #
    @4
    @116
    wceq
    #
    wi
    #
    wi
    va
    vb
    @3
    @14
    @26
    @26
    @108
    @3
    wceq
    #
    @111
    @69
    @118
    @125
    @126
    @110
    @66
    @68
    clt
    @126
    @109
    @65
    chash
    @108
    @3
    cS
    fveq2
    #
    fveq2d
    breq1d
    @126
    @114
    @123
    @117
    @124
    @126
    @109
    @65
    @113
    @127
    eqeq1d
    @126
    @115
    @4
    @116
    cc0
    @108
    @3
    fveq1
    eqeq1d
    imbi12d
    imbi12d
    @112
    @14
    wceq
    #
    @125
    @121
    @69
    @128
    @123
    @71
    @124
    @72
    @128
    @113
    @70
    @65
    @112
    @14
    cS
    fveq2
    eqeq2d
    @128
    @116
    @15
    @4
    cc0
    @112
    @14
    fveq1
    eqeq2d
    imbi12d
    imbi2d
    rspc2va
    syl21anc
    mp2d
    wph
    @8
    cS
    cfv
    #
    chash
    cfv
    #
    @68
    clt
    wbr
    #
    @129
    @18
    cS
    cfv
    #
    wceq
    #
    @9
    @19
    wceq
    #
    wph
    @16
    chash
    cfv
    #
    @135
    c2
    caddc
    co
    #
    @130
    @68
    clt
    wph
    @135
    cr
    wcel
    @75
    @135
    @136
    clt
    wbr
    wph
    @135
    wph
    @16
    @77
    wcel
    @135
    cn0
    wcel
    wph
    cW
    @77
    @16
    @78
    @64
    sseldi
    @76
    @16
    lencl
    syl
    nn0red
    2rp
    @135
    c2
    ltaddrp
    sylancl
    wph
    @129
    @16
    chash
    wph
    @129
    @8
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @8
    cfv
    #
    cL
    @8
    cfv
    #
    @16
    wph
    @8
    @26
    wcel
    #
    @129
    @139
    wceq
    wph
    @54
    @6
    c1
    @5
    cfz
    co
    #
    wcel
    #
    @141
    efgredlem.3
    wph
    @143
    @45
    @6
    @5
    cle
    wbr
    #
    @62
    wph
    @5
    wph
    @5
    @59
    nn0red
    lem1d
    wph
    @58
    @143
    @45
    @144
    wa
    wb
    @60
    @6
    @5
    fznn
    syl
    mpbir2and
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
    cB
    cI
    cM
    @6
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsres
    syl2anc
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
    efgsval
    syl
    wph
    @138
    cL
    @8
    wph
    @138
    @61
    cL
    wph
    @137
    @6
    c1
    cmin
    wph
    cB
    cc0
    @6
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    @137
    @6
    wph
    @147
    @8
    chash
    wph
    @53
    @6
    cc0
    @5
    cfz
    co
    #
    wcel
    #
    @147
    @8
    wceq
    @56
    wph
    @142
    @149
    @6
    @93
    @142
    @149
    wss
    1eluzge0
    c1
    cc0
    @5
    fzss1
    ax-mp
    @145
    sseldi
    #
    cW
    cB
    @6
    swrd0val
    syl2anc
    fveq2d
    wph
    @53
    @150
    @148
    @6
    wceq
    @56
    @151
    cW
    cB
    @6
    swrd0len
    syl2anc
    eqtr3d
    oveq1d
    efgredlemb.l
    syl6eqr
    fveq2d
    wph
    cL
    @7
    wcel
    @140
    @16
    wceq
    @63
    cL
    @7
    cB
    fvres
    syl
    3eqtrd
    #
    fveq2d
    wph
    @16
    cW
    wcel
    #
    @67
    @16
    cT
    cfv
    #
    crn
    #
    wcel
    @68
    @136
    wceq
    @64
    wph
    @67
    @61
    cB
    cfv
    #
    cT
    cfv
    #
    crn
    #
    @155
    wph
    @67
    cB
    cS
    cfv
    #
    @158
    efgredlem.4
    wph
    @54
    @45
    @159
    @158
    wcel
    efgredlem.3
    @62
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
    efgsdmi
    syl2anc
    eqeltrd
    @154
    @157
    @16
    @156
    cT
    cL
    @61
    cB
    efgredlemb.l
    fveq2i
    fveq2i
    rneqi
    syl6eleqr
    vy
    vz
    vw
    vv
    @67
    c.sm
    cT
    vn
    cI
    cM
    cW
    @16
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtlen
    syl2anc
    3brtr4d
    wph
    @129
    @16
    @132
    @152
    wph
    @22
    @153
    @18
    @26
    wcel
    #
    @132
    @16
    wceq
    @33
    @64
    wph
    @27
    @105
    @160
    efgredlemd.c
    wph
    @104
    @105
    @106
    simprd
    vx
    vy
    vz
    vw
    vv
    vt
    @16
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cC
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
    cC
    @16
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
    eqtr4d
    wph
    @141
    @160
    @120
    @131
    @133
    @134
    wi
    #
    wi
    #
    @146
    @161
    efgredlem.1
    @119
    @163
    @131
    @129
    @113
    wceq
    #
    @9
    @116
    wceq
    #
    wi
    #
    wi
    va
    vb
    @8
    @18
    @26
    @26
    @108
    @8
    wceq
    #
    @111
    @131
    @118
    @166
    @167
    @110
    @130
    @68
    clt
    @167
    @109
    @129
    chash
    @108
    @8
    cS
    fveq2
    #
    fveq2d
    breq1d
    @167
    @114
    @164
    @117
    @165
    @167
    @109
    @129
    @113
    @168
    eqeq1d
    @167
    @115
    @9
    @116
    cc0
    @108
    @8
    fveq1
    eqeq1d
    imbi12d
    imbi12d
    @112
    @18
    wceq
    #
    @166
    @162
    @131
    @169
    @164
    @133
    @165
    @134
    @169
    @113
    @132
    @129
    @112
    @18
    cS
    fveq2
    eqeq2d
    @169
    @116
    @19
    @9
    cc0
    @112
    @18
    fveq1
    eqeq2d
    imbi12d
    imbi2d
    rspc2va
    syl21anc
    mp2d
    3eqtr4d
    wph
    cc0
    @2
    wcel
    #
    @4
    @10
    wceq
    wph
    @44
    @170
    @47
    @1
    lbfzo0
    sylibr
    cc0
    @2
    cA
    fvres
    syl
    wph
    cc0
    @7
    wcel
    #
    @9
    @11
    wceq
    wph
    @45
    @171
    @62
    @6
    lbfzo0
    sylibr
    cc0
    @7
    cB
    fvres
    syl
    3eqtr3d
end
