include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wer.mm"
include "cfv.mm"
include "crn.mm"
include "cec.mm"
include "wss.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "efgval2.mm"
include "wrel.mm"
include "cpr.mm"
include "cconcat.mm"
include "co.mm"
include "wbr.mm"
include "relopabi.mm"
include "a1i.mm"
include "efgcpbllema.mm"
include "simp2bi.mm"
include "adantl.mm"
include "simp1bi.mm"
include "efger.mm"
include "simp3bi.mm"
include "ersym.mm"
include "syl3anbrc.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ertrd.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "simpll.mm"
include "sseldi.mm"
include "simpr.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "simplr.mm"
include "wceq.mm"
include "cvv.mm"
include "efgrcl.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "eleqtrrd.mm"
include "erref.mm"
include "ex.mm"
include "pm4.71d.mm"
include "w3a.mm"
include "df-3an.mm"
include "anidm.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "syl6bbr.mm"
include "iserd.mm"
include "wrex.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "efgtf.mm"
include "ffn.mm"
include "ovelrn.mm"
include "3syl.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simprr.mm"
include "fovrnd.mm"
include "adantr.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "swrdcl.mm"
include "syl.mm"
include "efgmf.mm"
include "ffvelrni.mm"
include "s2cld.mm"
include "ccatass.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "efgtval.mm"
include "splval.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfznn0.mm"
include "uzaddcl.mm"
include "ccatlen.mm"
include "cz.mm"
include "elfzuz3.mm"
include "nn0zd.mm"
include "eluzadd.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "eqeltrd.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "c0.mm"
include "wrd0.mm"
include "ccatrid.mm"
include "eluzfz1.mm"
include "eluzfz2.mm"
include "ccatswrd.mm"
include "swrdid.mm"
include "3eqtr2rd.mm"
include "swrd0len.mm"
include "eqtr2d.mm"
include "hash0.mm"
include "oveq2i.mm"
include "nn0addcld.mm"
include "addid1d.mm"
include "syl5req.mm"
include "splval2.mm"
include "3eqtr4d.mm"
include "fnovrn.mm"
include "efgi2.mm"
include "vex.mm"
include "elec.mm"
include "breq2.mm"
include "syl5bb.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ralrimiva.mm"
include "fvex.mm"
include "eqeltri.mm"
include "erex.mm"
include "mpisyl.mm"
include "ereq1.mm"
include "eceq2.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elabg.mm"
include "mpbir2and.mm"
include "intss1.mm"
include "syl5eqss.mm"

theorem efgcpbllemb
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
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cI: class I
  let cL: class L
  let cM: class M
  let cW: class W
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let cJ: class J
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
  assume efgcpbllem.1: |- L = { <. i , j >. | ( { i , j } C_ W /\ ( ( A ++ i ) ++ B ) .~ ( ( A ++ j ) ++ B ) ) }

  disjoint i j
  disjoint A i
  disjoint A j
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
  disjoint i k
  disjoint T i
  disjoint j k
  disjoint T j
  disjoint k m
  disjoint k t
  disjoint k x
  disjoint T k
  disjoint T m
  disjoint T t
  disjoint T x
  disjoint i y
  disjoint i z
  disjoint W i
  disjoint j y
  disjoint j z
  disjoint W j
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
  disjoint .~ i
  disjoint .~ j
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint B i
  disjoint B j
  disjoint S i
  disjoint S j
  disjoint I i
  disjoint I j
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint D i
  disjoint D j
  disjoint D m
  disjoint D t
  disjoint L c
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
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint j r
  disjoint j s
  disjoint j u
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
  disjoint i o
  disjoint j o
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
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- ( ( A e. W /\ B e. W ) -> .~ C_ L )

  proof
    cA
    cW
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    c.sm
    cW
    vr
    cv
    #
    wer
    #
    vf
    cv
    #
    cT
    cfv
    #
    crn
    #
    @5
    @3
    cec
    #
    wss
    #
    vf
    cW
    wral
    #
    wa
    #
    vr
    cab
    #
    cint
    #
    cL
    vf
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
    vr
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgval2
    @2
    cL
    @12
    wcel
    #
    @13
    cL
    wss
    @2
    @14
    cW
    cL
    wer
    #
    @7
    @5
    cL
    cec
    #
    wss
    #
    vf
    cW
    wral
    #
    @2
    vf
    vg
    vh
    cW
    cL
    cL
    wrel
    @2
    vi
    cv
    #
    vj
    cv
    #
    cpr
    cW
    wss
    cA
    @19
    cconcat
    co
    cB
    cconcat
    co
    cA
    @20
    cconcat
    co
    cB
    cconcat
    co
    c.sm
    wbr
    wa
    vi
    vj
    cL
    efgcpbllem.1
    relopabi
    a1i
    @2
    @5
    vg
    cv
    #
    cL
    wbr
    #
    wa
    #
    @21
    cW
    wcel
    #
    @5
    cW
    wcel
    #
    cA
    @21
    cconcat
    co
    cB
    cconcat
    co
    #
    cA
    @5
    cconcat
    co
    #
    cB
    cconcat
    co
    #
    c.sm
    wbr
    @21
    @5
    cL
    wbr
    @22
    @24
    @2
    @22
    @25
    @24
    @28
    @26
    c.sm
    wbr
    #
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
    vi
    vj
    vk
    vm
    vn
    cI
    cL
    cM
    cW
    @5
    @21
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbllem.1
    efgcpbllema
    #
    simp2bi
    adantl
    @22
    @25
    @2
    @22
    @25
    @24
    @29
    @30
    simp1bi
    #
    adantl
    @23
    @28
    @26
    c.sm
    cW
    cW
    c.sm
    wer
    #
    @23
    c.sm
    cI
    cW
    efgval.w
    efgval.r
    efger
    #
    a1i
    @22
    @29
    @2
    @22
    @25
    @24
    @29
    @30
    simp3bi
    #
    adantl
    ersym
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
    vi
    vj
    vk
    vm
    vn
    cI
    cL
    cM
    cW
    @21
    @5
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbllem.1
    efgcpbllema
    syl3anbrc
    @2
    @22
    @21
    vh
    cv
    #
    cL
    wbr
    #
    wa
    wa
    #
    @25
    @35
    cW
    wcel
    #
    @28
    cA
    @35
    cconcat
    co
    cB
    cconcat
    co
    #
    c.sm
    wbr
    @5
    @35
    cL
    wbr
    @22
    @25
    @2
    @36
    @31
    ad2antrl
    @36
    @38
    @2
    @22
    @36
    @24
    @38
    @26
    @39
    c.sm
    wbr
    #
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
    vi
    vj
    vk
    vm
    vn
    cI
    cL
    cM
    cW
    @21
    @35
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbllem.1
    efgcpbllema
    #
    simp2bi
    ad2antll
    @37
    @28
    @26
    @39
    c.sm
    cW
    @32
    @37
    @33
    a1i
    @22
    @29
    @2
    @36
    @34
    ad2antrl
    @36
    @40
    @2
    @22
    @36
    @24
    @38
    @40
    @41
    simp3bi
    ad2antll
    ertrd
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
    vi
    vj
    vk
    vm
    vn
    cI
    cL
    cM
    cW
    @5
    @35
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbllem.1
    efgcpbllema
    syl3anbrc
    @2
    @25
    @25
    @28
    @28
    c.sm
    wbr
    #
    wa
    #
    @5
    @5
    cL
    wbr
    #
    @2
    @25
    @42
    @2
    @25
    @42
    @2
    @25
    wa
    #
    @28
    c.sm
    cW
    @32
    @45
    @33
    a1i
    @45
    @28
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    @45
    @27
    @47
    wcel
    #
    cB
    @47
    wcel
    #
    @28
    @47
    wcel
    @45
    cA
    @47
    wcel
    #
    @5
    @47
    wcel
    #
    @48
    @45
    cW
    @47
    cA
    cW
    @47
    cid
    cfv
    #
    @47
    efgval.w
    @47
    fviss
    eqsstri
    #
    @0
    @1
    @25
    simpll
    #
    sseldi
    @45
    cW
    @47
    @5
    @53
    @2
    @25
    simpr
    sseldi
    #
    @46
    cA
    @5
    ccatcl
    syl2anc
    #
    @45
    cW
    @47
    cB
    @53
    @0
    @1
    @25
    simplr
    sseldi
    #
    @46
    @27
    cB
    ccatcl
    syl2anc
    @0
    cW
    @47
    wceq
    #
    @1
    @25
    @0
    cI
    cvv
    wcel
    @58
    cA
    cI
    cW
    efgval.w
    efgrcl
    simprd
    ad2antrr
    eleqtrrd
    #
    erref
    ex
    pm4.71d
    @44
    @25
    @25
    @42
    w3a
    @25
    @25
    wa
    #
    @42
    wa
    @43
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
    vi
    vj
    vk
    vm
    vn
    cI
    cL
    cM
    cW
    @5
    @5
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbllem.1
    efgcpbllema
    @25
    @25
    @42
    df-3an
    @60
    @25
    @42
    @25
    anidm
    anbi1i
    3bitri
    syl6bbr
    iserd
    #
    @2
    @17
    vf
    cW
    @45
    va
    @7
    @16
    @45
    va
    cv
    #
    @7
    wcel
    #
    @62
    vc
    cv
    #
    vu
    cv
    #
    @6
    co
    #
    wceq
    #
    vu
    @46
    wrex
    vc
    cc0
    @5
    chash
    cfv
    #
    cfz
    co
    #
    wrex
    #
    @62
    @16
    wcel
    #
    @45
    @69
    @46
    cxp
    #
    cW
    @6
    wf
    #
    @6
    @72
    wfn
    @63
    @70
    wb
    @25
    @73
    @2
    @25
    @6
    va
    vb
    @69
    @46
    @5
    @62
    @62
    vb
    cv
    #
    @74
    cM
    cfv
    cs2
    cotp
    #
    csplice
    co
    cmpt2
    wceq
    @73
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
    @5
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    simprd
    #
    adantl
    @72
    cW
    @6
    ffn
    vc
    vu
    @69
    @46
    @62
    @6
    ovelrn
    3syl
    @45
    @67
    @71
    vc
    vu
    @69
    @46
    @45
    @64
    @69
    wcel
    #
    @65
    @46
    wcel
    #
    wa
    #
    wa
    #
    @71
    @67
    @5
    @66
    cL
    wbr
    #
    @80
    @25
    @66
    cW
    wcel
    @28
    cA
    @66
    cconcat
    co
    #
    cB
    cconcat
    co
    #
    c.sm
    wbr
    #
    @81
    @2
    @25
    @79
    simplr
    #
    @80
    @64
    @65
    cW
    @69
    @46
    @6
    @25
    @73
    @2
    @79
    @76
    ad2antlr
    @45
    @77
    @78
    simprl
    #
    @45
    @77
    @78
    simprr
    #
    fovrnd
    @80
    @28
    cW
    wcel
    #
    @83
    @28
    cT
    cfv
    #
    crn
    #
    wcel
    @84
    @45
    @88
    @79
    @59
    adantr
    #
    @80
    @83
    cA
    chash
    cfv
    #
    @64
    caddc
    co
    #
    @65
    @89
    co
    #
    @90
    @80
    cA
    @5
    cc0
    @64
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    @65
    @65
    cM
    cfv
    #
    cs2
    #
    cconcat
    co
    #
    @5
    @64
    @68
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cB
    cconcat
    co
    #
    @99
    @100
    cB
    cconcat
    co
    #
    cconcat
    co
    #
    @83
    @94
    @80
    @99
    @47
    wcel
    #
    @100
    @47
    wcel
    #
    @49
    @102
    @104
    wceq
    @80
    @96
    @47
    wcel
    #
    @98
    @47
    wcel
    #
    @105
    @80
    @50
    @95
    @47
    wcel
    #
    @107
    @80
    cW
    @47
    cA
    @53
    @45
    @0
    @79
    @54
    adantr
    sseldi
    #
    @80
    @51
    @109
    @45
    @51
    @79
    @55
    adantr
    #
    @46
    @5
    cc0
    @64
    swrdcl
    syl
    #
    @46
    cA
    @95
    ccatcl
    syl2anc
    #
    @80
    @65
    @97
    @46
    @87
    @78
    @97
    @46
    wcel
    @45
    @77
    @46
    @46
    @65
    cM
    vy
    vz
    cI
    cM
    efgval2.m
    efgmf
    ffvelrni
    ad2antll
    s2cld
    #
    @46
    @96
    @98
    ccatcl
    syl2anc
    @80
    @51
    @106
    @111
    @46
    @5
    @64
    @68
    swrdcl
    syl
    #
    @45
    @49
    @79
    @57
    adantr
    #
    @46
    @99
    @100
    cB
    ccatass
    syl3anc
    @80
    @82
    @101
    cB
    cconcat
    @80
    cA
    @95
    @98
    cconcat
    co
    #
    cconcat
    co
    #
    @100
    cconcat
    co
    #
    cA
    @117
    @100
    cconcat
    co
    #
    cconcat
    co
    #
    @101
    @82
    @80
    @50
    @117
    @47
    wcel
    #
    @106
    @119
    @121
    wceq
    @110
    @80
    @109
    @108
    @122
    @112
    @114
    @46
    @95
    @98
    ccatcl
    syl2anc
    @115
    @46
    cA
    @117
    @100
    ccatass
    syl3anc
    @80
    @99
    @118
    @100
    cconcat
    @80
    @50
    @109
    @108
    @99
    @118
    wceq
    @110
    @112
    @114
    @46
    cA
    @95
    @98
    ccatass
    syl3anc
    oveq1d
    @80
    @66
    @120
    cA
    cconcat
    @80
    @66
    @5
    @64
    @64
    @98
    cotp
    csplice
    co
    #
    @120
    @80
    @25
    @77
    @78
    @66
    @123
    wceq
    @85
    @86
    @87
    vy
    vz
    vw
    vv
    @65
    c.sm
    cT
    vn
    cI
    cM
    @64
    cW
    @5
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    @80
    @25
    @77
    @77
    @108
    @123
    @120
    wceq
    @85
    @86
    @86
    @114
    @98
    @5
    @64
    @64
    cW
    @69
    @69
    @47
    splval
    syl13anc
    eqtrd
    oveq2d
    3eqtr4rd
    oveq1d
    @80
    @94
    @28
    @93
    @93
    @98
    cotp
    csplice
    co
    #
    @104
    @80
    @88
    @93
    cc0
    @28
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @78
    @94
    @124
    wceq
    @91
    @80
    @93
    cc0
    cuz
    cfv
    #
    wcel
    #
    @125
    @93
    cuz
    cfv
    #
    wcel
    @127
    @80
    @92
    @128
    wcel
    @64
    cn0
    wcel
    #
    @129
    @80
    @92
    cn0
    @128
    @80
    @50
    @92
    cn0
    wcel
    @110
    @46
    cA
    lencl
    syl
    #
    nn0uz
    syl6eleq
    @77
    @131
    @45
    @78
    @64
    @68
    elfznn0
    ad2antrl
    #
    @64
    cc0
    @92
    uzaddcl
    syl2anc
    @80
    @125
    @27
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    caddc
    co
    #
    @130
    @80
    @48
    @49
    @125
    @136
    wceq
    @45
    @48
    @79
    @56
    adantr
    @116
    @46
    @27
    cB
    ccatlen
    syl2anc
    @80
    @134
    @130
    wcel
    @135
    cn0
    wcel
    #
    @136
    @130
    wcel
    @80
    @134
    @92
    @68
    caddc
    co
    #
    @130
    @80
    @50
    @51
    @134
    @138
    wceq
    @110
    @111
    @46
    cA
    @5
    ccatlen
    syl2anc
    @80
    @68
    @92
    caddc
    co
    #
    @64
    @92
    caddc
    co
    #
    cuz
    cfv
    #
    @138
    @130
    @80
    @68
    @64
    cuz
    cfv
    wcel
    #
    @92
    cz
    wcel
    @139
    @141
    wcel
    @77
    @142
    @45
    @78
    @64
    cc0
    @68
    elfzuz3
    ad2antrl
    @80
    @92
    @132
    nn0zd
    @92
    @64
    @68
    eluzadd
    syl2anc
    @80
    @68
    @92
    @80
    @68
    @80
    @51
    @68
    cn0
    wcel
    @111
    @46
    @5
    lencl
    syl
    #
    nn0cnd
    @80
    @92
    @132
    nn0cnd
    #
    addcomd
    @80
    @140
    @93
    cuz
    @80
    @64
    @92
    @80
    @64
    @133
    nn0cnd
    @144
    addcomd
    fveq2d
    3eltr3d
    eqeltrd
    @80
    @49
    @137
    @116
    @46
    cB
    lencl
    syl
    @135
    @93
    @134
    uzaddcl
    syl2anc
    eqeltrd
    @93
    cc0
    @125
    elfzuzb
    sylanbrc
    #
    @87
    vy
    vz
    vw
    vv
    @65
    c.sm
    cT
    vn
    cI
    cM
    @93
    cW
    @28
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    @80
    @96
    c0
    @103
    @98
    @28
    @93
    @93
    @46
    @113
    c0
    @47
    wcel
    @80
    @46
    wrd0
    a1i
    @80
    @106
    @49
    @103
    @47
    wcel
    @115
    @116
    @46
    @100
    cB
    ccatcl
    syl2anc
    @114
    @80
    @96
    c0
    cconcat
    co
    #
    @103
    cconcat
    co
    @96
    @103
    cconcat
    co
    #
    @96
    @100
    cconcat
    co
    #
    cB
    cconcat
    co
    #
    @28
    @80
    @146
    @96
    @103
    cconcat
    @80
    @107
    @146
    @96
    wceq
    @113
    @46
    @96
    ccatrid
    syl
    oveq1d
    @80
    @107
    @106
    @49
    @149
    @147
    wceq
    @113
    @115
    @116
    @46
    @96
    @100
    cB
    ccatass
    syl3anc
    @80
    @148
    @27
    cB
    cconcat
    @80
    @148
    cA
    @95
    @100
    cconcat
    co
    #
    cconcat
    co
    #
    @27
    @80
    @50
    @109
    @106
    @148
    @151
    wceq
    @110
    @112
    @115
    @46
    cA
    @95
    @100
    ccatass
    syl3anc
    @80
    @150
    @5
    cA
    cconcat
    @80
    @150
    @5
    cc0
    @68
    cop
    csubstr
    co
    #
    @5
    @80
    @51
    cc0
    cc0
    @64
    cfz
    co
    wcel
    #
    @77
    @68
    @69
    wcel
    #
    @150
    @152
    wceq
    @111
    @80
    @64
    @128
    wcel
    @153
    @80
    @64
    cn0
    @128
    @133
    nn0uz
    syl6eleq
    cc0
    @64
    eluzfz1
    syl
    @86
    @80
    @68
    @128
    wcel
    @154
    @80
    @68
    cn0
    @128
    @143
    nn0uz
    syl6eleq
    cc0
    @68
    eluzfz2
    syl
    @46
    @5
    cc0
    @64
    @68
    ccatswrd
    syl13anc
    @80
    @51
    @152
    @5
    wceq
    @111
    @46
    @5
    swrdid
    syl
    eqtrd
    oveq2d
    eqtrd
    oveq1d
    3eqtr2rd
    @80
    @96
    chash
    cfv
    #
    @92
    @95
    chash
    cfv
    #
    caddc
    co
    #
    @93
    @80
    @50
    @109
    @155
    @157
    wceq
    @110
    @112
    @46
    cA
    @95
    ccatlen
    syl2anc
    @80
    @156
    @64
    @92
    caddc
    @80
    @51
    @77
    @156
    @64
    wceq
    @111
    @86
    @46
    @5
    @64
    swrd0len
    syl2anc
    oveq2d
    eqtr2d
    @80
    @93
    c0
    chash
    cfv
    #
    caddc
    co
    @93
    cc0
    caddc
    co
    @93
    @158
    cc0
    @93
    caddc
    hash0
    oveq2i
    @80
    @93
    @80
    @93
    @80
    @92
    @64
    @132
    @133
    nn0addcld
    nn0cnd
    addid1d
    syl5req
    splval2
    eqtrd
    3eqtr4d
    @80
    @89
    @126
    @46
    cxp
    #
    wfn
    #
    @127
    @78
    @94
    @90
    wcel
    @80
    @88
    @159
    cW
    @89
    wf
    #
    @160
    @91
    @88
    @89
    va
    vb
    @126
    @46
    @28
    @75
    csplice
    co
    cmpt2
    wceq
    @161
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
    @28
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    simprd
    @159
    cW
    @89
    ffn
    3syl
    @145
    @87
    @126
    @46
    @93
    @65
    @89
    fnovrn
    syl3anc
    eqeltrd
    vy
    vz
    vw
    vv
    @28
    @83
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
    vi
    vj
    vk
    vm
    vn
    cI
    cL
    cM
    cW
    @5
    @66
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbllem.1
    efgcpbllema
    syl3anbrc
    @71
    @5
    @62
    cL
    wbr
    @67
    @81
    @62
    @5
    cL
    va
    vex
    vf
    vex
    elec
    @62
    @66
    @5
    cL
    breq2
    syl5bb
    syl5ibrcom
    rexlimdvva
    sylbid
    ssrdv
    ralrimiva
    @2
    cL
    cvv
    wcel
    #
    @14
    @15
    @18
    wa
    #
    wb
    @2
    @15
    cW
    cvv
    wcel
    @162
    @61
    cW
    @52
    cvv
    efgval.w
    @47
    cid
    fvex
    eqeltri
    cW
    cL
    cvv
    erex
    mpisyl
    @11
    @163
    vr
    cL
    cvv
    @3
    cL
    wceq
    #
    @4
    @15
    @10
    @18
    cW
    @3
    cL
    ereq1
    @164
    @9
    @17
    vf
    cW
    @164
    @8
    @16
    @7
    @3
    cL
    @5
    eceq2
    sseq2d
    ralbidv
    anbi12d
    elabg
    syl
    mpbir2and
    cL
    @12
    intss1
    syl
    syl5eqss
end
