include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "cres.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cn0.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "wf.mm"
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
include "wrdf.mm"
include "cfz.mm"
include "cle.mm"
include "cn.mm"
include "efgredlema.mm"
include "simpld.mm"
include "nnm1nn0.mm"
include "nnred.mm"
include "lem1d.mm"
include "wa.mm"
include "wb.mm"
include "wne.mm"
include "eldifsni.mm"
include "3syl.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "fznn0.mm"
include "mpbir2and.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "nn0red.mm"
include "2rp.mm"
include "ltaddrp.mm"
include "sylancl.mm"
include "fznn.mm"
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
include "fzo0end.mm"
include "fvres.mm"
include "3eqtrd.mm"
include "efgsdmi.mm"
include "efgtlen.mm"
include "3brtr4d.mm"
include "wrex.mm"
include "wfn.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "efgtf.mm"
include "simprd.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mpbid.mm"
include "elfzofz.mm"
include "reeanv.mm"
include "wi.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "eqid.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "efgredlemb.mm"
include "iman.mm"
include "mpbir.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "3eqtr4d.mm"
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
include "lbfzo0.mm"
include "sylibr.mm"
include "3eqtr3d.mm"
include "pm2.65i.mm"

theorem efgredlem
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
  assume efgredlem.1: |- ( ph -> A. a e. dom S A. b e. dom S ( ( # ` ( S ` a ) ) < ( # ` ( S ` A ) ) -> ( ( S ` a ) = ( S ` b ) -> ( a ` 0 ) = ( b ` 0 ) ) ) )
  assume efgredlem.2: |- ( ph -> A e. dom S )
  assume efgredlem.3: |- ( ph -> B e. dom S )
  assume efgredlem.4: |- ( ph -> ( S ` A ) = ( S ` B ) )
  assume efgredlem.5: |- ( ph -> -. ( A ` 0 ) = ( B ` 0 ) )

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint a z
  disjoint b y
  disjoint b z
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
  assert |- -. ph

  proof
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
    @0
    @1
    wph
    @6
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
    @13
    @11
    cS
    cfv
    #
    wceq
    #
    @7
    @12
    wceq
    #
    wph
    @4
    c1
    cmin
    co
    #
    cA
    cfv
    #
    chash
    cfv
    #
    @23
    c2
    caddc
    co
    #
    @14
    @16
    clt
    wph
    @23
    cr
    wcel
    c2
    crp
    wcel
    @23
    @24
    clt
    wbr
    wph
    @23
    wph
    @22
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    @23
    cn0
    wcel
    wph
    cW
    @26
    @22
    cW
    @26
    cid
    cfv
    @26
    efgval.w
    @26
    fviss
    eqsstri
    wph
    cc0
    @3
    cfzo
    co
    #
    cW
    @21
    cA
    wph
    cA
    cW
    cword
    #
    wcel
    #
    @27
    cW
    cA
    wf
    wph
    cA
    @28
    c0
    csn
    #
    wph
    cA
    cS
    cdm
    #
    wcel
    #
    cA
    @28
    @30
    cdif
    #
    wcel
    #
    efgredlem.2
    @32
    @34
    @0
    cD
    wcel
    vi
    cv
    #
    cA
    cfv
    @35
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
    @3
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
    #
    syl
    eldifad
    #
    cW
    cA
    wrdf
    syl
    wph
    @21
    cc0
    @4
    cfz
    co
    #
    @27
    wph
    @21
    @39
    wcel
    #
    @21
    cn0
    wcel
    #
    @21
    @4
    cle
    wbr
    #
    wph
    @4
    cn
    wcel
    #
    @41
    wph
    @43
    @9
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
    @4
    nnm1nn0
    syl
    wph
    @4
    wph
    @4
    @46
    nnred
    lem1d
    wph
    @3
    cn
    wcel
    #
    @4
    cn0
    wcel
    @40
    @41
    @42
    wa
    wb
    wph
    @47
    cA
    c0
    wne
    #
    wph
    @32
    @34
    @48
    efgredlem.2
    @37
    cA
    @28
    c0
    eldifsni
    3syl
    wph
    @29
    cA
    cfn
    wcel
    @47
    @48
    wb
    @38
    cW
    cA
    wrdfin
    cA
    hashnncl
    3syl
    mpbird
    @3
    nnm1nn0
    @21
    @4
    fznn0
    3syl
    mpbir2and
    wph
    @3
    cz
    wcel
    #
    @27
    @39
    wceq
    wph
    @3
    wph
    @29
    @3
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
    @3
    fzoval
    syl
    eleqtrrd
    ffvelrnd
    #
    sseldi
    @25
    @22
    lencl
    syl
    nn0red
    2rp
    @23
    c2
    ltaddrp
    sylancl
    wph
    @13
    @22
    chash
    wph
    @13
    @6
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @6
    cfv
    #
    @21
    @6
    cfv
    #
    @22
    wph
    @6
    @31
    wcel
    #
    @13
    @55
    wceq
    wph
    @32
    @4
    c1
    @3
    cfz
    co
    #
    wcel
    #
    @57
    efgredlem.2
    wph
    @59
    @43
    @4
    @3
    cle
    wbr
    #
    @46
    wph
    @3
    wph
    @3
    @50
    nn0red
    lem1d
    wph
    @49
    @59
    @43
    @60
    wa
    wb
    @51
    @4
    @3
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
    @4
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
    @6
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
    #
    wph
    @54
    @21
    @6
    wph
    @53
    @4
    c1
    cmin
    wph
    cA
    cc0
    @4
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    @53
    @4
    wph
    @64
    @6
    chash
    wph
    @29
    @4
    cc0
    @3
    cfz
    co
    #
    wcel
    #
    @64
    @6
    wceq
    @38
    wph
    @58
    @66
    @4
    c1
    cc0
    cuz
    cfv
    wcel
    #
    @58
    @66
    wss
    1eluzge0
    c1
    cc0
    @3
    fzss1
    ax-mp
    @61
    sseldi
    #
    cW
    cA
    @4
    swrd0val
    syl2anc
    fveq2d
    wph
    @29
    @67
    @65
    @4
    wceq
    @38
    @69
    cW
    cA
    @4
    swrd0len
    syl2anc
    eqtr3d
    oveq1d
    fveq2d
    #
    wph
    @43
    @21
    @5
    wcel
    @56
    @22
    wceq
    @46
    @4
    fzo0end
    @21
    @5
    cA
    fvres
    3syl
    #
    3eqtrd
    fveq2d
    wph
    @22
    cW
    wcel
    #
    @15
    @22
    cT
    cfv
    #
    crn
    wcel
    #
    @16
    @24
    wceq
    @52
    wph
    @32
    @43
    @74
    efgredlem.2
    @46
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
    #
    vy
    vz
    vw
    vv
    @15
    c.sm
    cT
    vn
    cI
    cM
    cW
    @22
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtlen
    syl2anc
    3brtr4d
    wph
    @55
    @11
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @11
    cfv
    #
    @13
    @18
    wph
    @56
    @9
    c1
    cmin
    co
    #
    @11
    cfv
    #
    @55
    @78
    wph
    @22
    @79
    cB
    cfv
    #
    @56
    @80
    wph
    @15
    @35
    vr
    cv
    #
    @73
    co
    wceq
    #
    vr
    @25
    wrex
    #
    vi
    cc0
    @23
    cfz
    co
    #
    wrex
    #
    cB
    cS
    cfv
    #
    vj
    cv
    #
    vs
    cv
    #
    @81
    cT
    cfv
    #
    co
    wceq
    #
    vs
    @25
    wrex
    #
    vj
    cc0
    @81
    chash
    cfv
    cfz
    co
    #
    wrex
    #
    @22
    @81
    wceq
    #
    wph
    @74
    @86
    @75
    wph
    @85
    @25
    cxp
    #
    cW
    @73
    wf
    #
    @73
    @96
    wfn
    @74
    @86
    wb
    wph
    @73
    va
    vb
    @85
    @25
    @22
    va
    cv
    #
    @98
    vb
    cv
    #
    @99
    cM
    cfv
    cs2
    cotp
    #
    csplice
    co
    cmpt2
    wceq
    #
    @97
    wph
    @72
    @101
    @97
    wa
    @52
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
    @22
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    syl
    simprd
    @96
    cW
    @73
    ffn
    vi
    vr
    @85
    @25
    @15
    @73
    ovelrn
    3syl
    mpbid
    wph
    @87
    @90
    crn
    wcel
    #
    @94
    wph
    cB
    @31
    wcel
    #
    @44
    @102
    efgredlem.3
    wph
    @43
    @44
    @45
    simprd
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
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsdmi
    syl2anc
    wph
    @93
    @25
    cxp
    #
    cW
    @90
    wf
    #
    @90
    @105
    wfn
    @102
    @94
    wb
    wph
    @90
    va
    vb
    @93
    @25
    @81
    @100
    csplice
    co
    cmpt2
    wceq
    #
    @106
    wph
    @81
    cW
    wcel
    @107
    @106
    wa
    wph
    cc0
    @8
    cfzo
    co
    #
    cW
    @79
    cB
    wph
    cB
    @28
    wcel
    #
    @108
    cW
    cB
    wf
    wph
    cB
    @28
    @30
    wph
    @103
    cB
    @33
    wcel
    #
    efgredlem.3
    @103
    @110
    @1
    cD
    wcel
    @35
    cB
    cfv
    @36
    cB
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @8
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
    @79
    cc0
    @9
    cfz
    co
    #
    @108
    wph
    @44
    @79
    @10
    wcel
    #
    @79
    @112
    wcel
    @104
    @9
    fzo0end
    #
    @79
    cc0
    @9
    elfzofz
    3syl
    wph
    @8
    cz
    wcel
    #
    @108
    @112
    wceq
    wph
    @8
    wph
    @109
    @8
    cn0
    wcel
    @111
    cW
    cB
    lencl
    syl
    #
    nn0zd
    #
    cc0
    @8
    fzoval
    syl
    eleqtrrd
    ffvelrnd
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
    @81
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    syl
    simprd
    @105
    cW
    @90
    ffn
    vj
    vs
    @93
    @25
    @87
    @90
    ovelrn
    3syl
    mpbid
    @86
    @94
    wa
    @84
    @92
    wa
    #
    vj
    @93
    wrex
    vi
    @85
    wrex
    wph
    @95
    @84
    @92
    vi
    vj
    @85
    @93
    reeanv
    wph
    @118
    @95
    vi
    vj
    @85
    @93
    @118
    @83
    @91
    wa
    #
    vs
    @25
    wrex
    vr
    @25
    wrex
    wph
    @35
    @85
    wcel
    #
    @88
    @93
    wcel
    #
    wa
    #
    wa
    #
    @95
    @83
    @91
    vr
    vs
    @25
    @25
    reeanv
    @123
    @119
    @95
    vr
    vs
    @25
    @25
    @123
    @82
    @25
    wcel
    #
    @89
    @25
    wcel
    #
    wa
    #
    @119
    @95
    @123
    @126
    @119
    wa
    #
    wa
    #
    @95
    wi
    @128
    @95
    wn
    #
    wa
    #
    wn
    @130
    vx
    vy
    vz
    vw
    vv
    vt
    cA
    cB
    cD
    @35
    @88
    c.sm
    cS
    cT
    @82
    vk
    vm
    vn
    cI
    @21
    @79
    cM
    @89
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
    @98
    cS
    cfv
    #
    chash
    cfv
    #
    @16
    clt
    wbr
    #
    @131
    @99
    cS
    cfv
    #
    wceq
    #
    cc0
    @98
    cfv
    #
    cc0
    @99
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    vb
    @31
    wral
    va
    @31
    wral
    #
    @122
    @127
    @129
    efgredlem.1
    ad3antrrr
    wph
    @32
    @122
    @127
    @129
    efgredlem.2
    ad3antrrr
    wph
    @103
    @122
    @127
    @129
    efgredlem.3
    ad3antrrr
    wph
    @15
    @87
    wceq
    @122
    @127
    @129
    efgredlem.4
    ad3antrrr
    wph
    @2
    wn
    @122
    @127
    @129
    efgredlem.5
    ad3antrrr
    @21
    eqid
    @79
    eqid
    @130
    @120
    @121
    wph
    @122
    @127
    @129
    simpllr
    #
    simpld
    @130
    @120
    @121
    @142
    simprd
    @130
    @124
    @125
    @123
    @126
    @119
    @129
    simplrl
    #
    simpld
    @130
    @124
    @125
    @143
    simprd
    @130
    @83
    @91
    @123
    @126
    @119
    @129
    simplrr
    #
    simpld
    @130
    @83
    @91
    @144
    simprd
    @128
    @129
    simpr
    efgredlemb
    @128
    @95
    iman
    mpbir
    expr
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    mp2and
    @71
    wph
    @44
    @113
    @80
    @81
    wceq
    @104
    @114
    @79
    @10
    cB
    fvres
    3syl
    3eqtr4d
    @70
    wph
    @77
    @79
    @11
    wph
    @76
    @9
    c1
    cmin
    wph
    cB
    cc0
    @9
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    @76
    @9
    wph
    @145
    @11
    chash
    wph
    @109
    @9
    cc0
    @8
    cfz
    co
    #
    wcel
    #
    @145
    @11
    wceq
    @111
    wph
    c1
    @8
    cfz
    co
    #
    @147
    @9
    @68
    @149
    @147
    wss
    1eluzge0
    c1
    cc0
    @8
    fzss1
    ax-mp
    wph
    @9
    @149
    wcel
    #
    @44
    @9
    @8
    cle
    wbr
    #
    @104
    wph
    @8
    wph
    @8
    @116
    nn0red
    lem1d
    wph
    @115
    @150
    @44
    @151
    wa
    wb
    @117
    @9
    @8
    fznn
    syl
    mpbir2and
    #
    sseldi
    #
    cW
    cB
    @9
    swrd0val
    syl2anc
    fveq2d
    wph
    @109
    @148
    @146
    @9
    wceq
    @111
    @153
    cW
    cB
    @9
    swrd0len
    syl2anc
    eqtr3d
    oveq1d
    fveq2d
    3eqtr4d
    @63
    wph
    @11
    @31
    wcel
    #
    @18
    @78
    wceq
    wph
    @103
    @150
    @154
    efgredlem.3
    @152
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
    @9
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
    @11
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
    3eqtr4d
    wph
    @57
    @154
    @141
    @17
    @19
    @20
    wi
    #
    wi
    #
    @62
    @155
    efgredlem.1
    @140
    @157
    @17
    @13
    @134
    wceq
    #
    @7
    @137
    wceq
    #
    wi
    #
    wi
    va
    vb
    @6
    @11
    @31
    @31
    @98
    @6
    wceq
    #
    @133
    @17
    @139
    @160
    @161
    @132
    @14
    @16
    clt
    @161
    @131
    @13
    chash
    @98
    @6
    cS
    fveq2
    #
    fveq2d
    breq1d
    @161
    @135
    @158
    @138
    @159
    @161
    @131
    @13
    @134
    @162
    eqeq1d
    @161
    @136
    @7
    @137
    cc0
    @98
    @6
    fveq1
    eqeq1d
    imbi12d
    imbi12d
    @99
    @11
    wceq
    #
    @160
    @156
    @17
    @163
    @158
    @19
    @159
    @20
    @163
    @134
    @18
    @13
    @99
    @11
    cS
    fveq2
    eqeq2d
    @163
    @137
    @12
    @7
    cc0
    @99
    @11
    fveq1
    eqeq2d
    imbi12d
    imbi2d
    rspc2va
    syl21anc
    mp2d
    wph
    cc0
    @5
    wcel
    #
    @7
    @0
    wceq
    wph
    @43
    @164
    @46
    @4
    lbfzo0
    sylibr
    cc0
    @5
    cA
    fvres
    syl
    wph
    cc0
    @10
    wcel
    #
    @12
    @1
    wceq
    wph
    @44
    @165
    @104
    @9
    lbfzo0
    sylibr
    cc0
    @10
    cB
    fvres
    syl
    3eqtr3d
    efgredlem.5
    pm2.65i
end
