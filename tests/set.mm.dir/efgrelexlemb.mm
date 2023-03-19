include "cv.mm"
include "wer.mm"
include "cfv.mm"
include "crn.mm"
include "cec.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "efgval2.mm"
include "wcel.mm"
include "wtru.mm"
include "wrel.mm"
include "cc0.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "relopabi.mm"
include "a1i.mm"
include "wbr.mm"
include "simpr.mm"
include "eqcom.mm"
include "2rexbii.mm"
include "rexcom.mm"
include "bitri.mm"
include "efgrelexlema.mm"
include "3bitr4i.mm"
include "sylib.mm"
include "reeanv.mm"
include "wi.mm"
include "cdm.mm"
include "wfn.mm"
include "wb.mm"
include "wfo.mm"
include "efgsfo.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fniniseg.mm"
include "eqtr3.mm"
include "w3a.mm"
include "efgred.mm"
include "eqcomd.mm"
include "3expa.mm"
include "sylan2.mm"
include "an4s.mm"
include "syl2anb.mm"
include "eqeq2.mm"
include "syl5ibcom.mm"
include "reximdv.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impd.mm"
include "rexlimiv.mm"
include "reximi.mm"
include "sylbir.mm"
include "sylibr.mm"
include "adantl.mm"
include "eqid.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "pm4.71i.mm"
include "bitr3i.mm"
include "rexbii2.mm"
include "forn.mm"
include "eleq2i.mm"
include "fvelrnb.mm"
include "3bitr4ri.mm"
include "iserd.mm"
include "trud.mm"
include "simpl.mm"
include "foelrn.mm"
include "sylancr.mm"
include "simprl.mm"
include "simprr.mm"
include "sylanbrc.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "simplr.mm"
include "fveq2d.mm"
include "rneqd.mm"
include "eleqtrd.mm"
include "efgsp1.mm"
include "syl2anc.mm"
include "cword.mm"
include "c0.mm"
include "cdif.mm"
include "c1.mm"
include "cmin.mm"
include "chash.mm"
include "cfzo.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "ad2antrl.mm"
include "eldifad.mm"
include "cfz.mm"
include "c2o.mm"
include "cxp.mm"
include "wf.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "efgtf.mm"
include "simprd.mm"
include "frn.mm"
include "syl.mm"
include "sselda.mm"
include "adantr.mm"
include "efgsval2.mm"
include "syl3anc.mm"
include "s1cld.mm"
include "cn.mm"
include "wne.mm"
include "eldifsn.mm"
include "lennncl.mm"
include "sylbi.mm"
include "lbfzo0.mm"
include "ccatval1.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "vex.mm"
include "elec.mm"
include "ssrdv.mm"
include "rgen.mm"
include "cvv.mm"
include "cid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "erex.mm"
include "mp2.mm"
include "ereq1.mm"
include "eceq2.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elab.mm"
include "mpbir2an.mm"
include "intss1.mm"
include "eqsstri.mm"

theorem efgrelexlemb
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
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let cA: class A
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
  let cB: class B
  let cC: class C
  let cY: class Y
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )
  assume efgval2.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume efgval2.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume efgred.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume efgred.s: |- S = ( m e. { t e. ( Word W \ { (/) } ) | ( ( t ` 0 ) e. D /\ A. k e. ( 1 ..^ ( # ` t ) ) ( t ` k ) e. ran ( T ` ( t ` ( k - 1 ) ) ) ) } |-> ( m ` ( ( # ` m ) - 1 ) ) )
  assume efgrelexlem.1: |- L = { <. i , j >. | E. c e. ( `' S " { i } ) E. d e. ( `' S " { j } ) ( c ` 0 ) = ( d ` 0 ) }

  disjoint c d
  disjoint c i
  disjoint c j
  disjoint d i
  disjoint d j
  disjoint i j
  disjoint y z
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
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
  disjoint c m
  disjoint c x
  disjoint M c
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
  disjoint c k
  disjoint T c
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
  disjoint W c
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint W d
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
  disjoint .~ c
  disjoint .~ d
  disjoint .~ i
  disjoint .~ j
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint I c
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
  disjoint D c
  disjoint D d
  disjoint D i
  disjoint D j
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
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c r
  disjoint c s
  disjoint c u
  disjoint A c
  disjoint d f
  disjoint d g
  disjoint d h
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
  disjoint c o
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
  disjoint d o
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
  disjoint S o
  disjoint S r
  disjoint S s
  disjoint S u
  disjoint Y i
  disjoint Y j
  disjoint I a
  disjoint I b
  disjoint I f
  disjoint I g
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D a
  disjoint D b
  disjoint D f
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- .~ C_ L

  proof
    c.sm
    cW
    vr
    cv
    #
    wer
    #
    va
    cv
    #
    cT
    cfv
    #
    crn
    #
    @2
    @0
    cec
    #
    wss
    #
    va
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
    va
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
    cL
    @9
    wcel
    #
    @10
    cL
    wss
    @11
    cW
    cL
    wer
    #
    @4
    @2
    cL
    cec
    #
    wss
    #
    va
    cW
    wral
    #
    @12
    wtru
    vf
    vg
    vh
    cW
    cL
    cL
    wrel
    wtru
    cc0
    vc
    cv
    cfv
    cc0
    vd
    cv
    cfv
    wceq
    vd
    cS
    ccnv
    #
    vj
    cv
    csn
    cima
    wrex
    vc
    @16
    vi
    cv
    #
    csn
    cima
    wrex
    vi
    vj
    cL
    efgrelexlem.1
    relopabi
    a1i
    wtru
    vf
    cv
    #
    vg
    cv
    #
    cL
    wbr
    #
    wa
    @20
    @19
    @18
    cL
    wbr
    #
    wtru
    @20
    simpr
    cc0
    @2
    cfv
    #
    cc0
    vb
    cv
    #
    cfv
    #
    wceq
    #
    vb
    @16
    @19
    csn
    cima
    #
    wrex
    #
    va
    @16
    @18
    csn
    cima
    #
    wrex
    #
    @24
    @22
    wceq
    #
    va
    @28
    wrex
    vb
    @26
    wrex
    #
    @20
    @21
    @29
    @30
    vb
    @26
    wrex
    va
    @28
    wrex
    @31
    @25
    @30
    va
    vb
    @28
    @26
    @22
    @24
    eqcom
    2rexbii
    @30
    va
    vb
    @28
    @26
    rexcom
    bitri
    vx
    vy
    vz
    vw
    vv
    vt
    @18
    @19
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
    va
    vb
    vc
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelexlem.1
    efgrelexlema
    #
    vx
    vy
    vz
    vw
    vv
    vt
    @19
    @18
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
    vb
    va
    vc
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelexlem.1
    efgrelexlema
    3bitr4i
    sylib
    @20
    @19
    vh
    cv
    #
    cL
    wbr
    #
    wa
    #
    @18
    @33
    cL
    wbr
    #
    wtru
    @35
    @22
    cc0
    vs
    cv
    #
    cfv
    #
    wceq
    #
    vs
    @16
    @33
    csn
    cima
    #
    wrex
    #
    va
    @28
    wrex
    #
    @36
    @20
    @29
    cc0
    @0
    cfv
    #
    @38
    wceq
    #
    vs
    @40
    wrex
    #
    vr
    @26
    wrex
    #
    @42
    @34
    @32
    vx
    vy
    vz
    vw
    vv
    vt
    @19
    @33
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
    vr
    vs
    vc
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelexlem.1
    efgrelexlema
    @29
    @46
    wa
    @27
    @45
    wa
    #
    vr
    @26
    wrex
    #
    va
    @28
    wrex
    @42
    @27
    @45
    va
    vr
    @28
    @26
    reeanv
    @48
    @41
    va
    @28
    @47
    @41
    vr
    @26
    @0
    @26
    wcel
    #
    @27
    @45
    @41
    @49
    @25
    @45
    @41
    wi
    #
    vb
    @26
    @49
    @23
    @26
    wcel
    #
    wa
    #
    @50
    @25
    @45
    @24
    @38
    wceq
    #
    vs
    @40
    wrex
    #
    wi
    @52
    @44
    @53
    vs
    @40
    @52
    @24
    @43
    wceq
    #
    @44
    @53
    @49
    @0
    cS
    cdm
    #
    wcel
    #
    @0
    cS
    cfv
    #
    @19
    wceq
    #
    wa
    #
    @23
    @56
    wcel
    #
    @23
    cS
    cfv
    #
    @19
    wceq
    #
    wa
    #
    @55
    @51
    cS
    @56
    wfn
    #
    @49
    @60
    wb
    @56
    cW
    cS
    wfo
    #
    @65
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
    #
    @56
    cW
    cS
    fofn
    ax-mp
    #
    @56
    @19
    @0
    cS
    fniniseg
    ax-mp
    @65
    @51
    @64
    wb
    @68
    @56
    @19
    @23
    cS
    fniniseg
    ax-mp
    @57
    @61
    @59
    @63
    @55
    @59
    @63
    wa
    @57
    @61
    wa
    @58
    @62
    wceq
    #
    @55
    @58
    @62
    @19
    eqtr3
    @57
    @61
    @69
    @55
    @57
    @61
    @69
    w3a
    @43
    @24
    vx
    vy
    vz
    vw
    vv
    vt
    @0
    @23
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
    efgred
    eqcomd
    3expa
    sylan2
    an4s
    syl2anb
    @43
    @38
    @24
    eqeq2
    syl5ibcom
    reximdv
    @25
    @41
    @54
    @45
    @25
    @39
    @53
    vs
    @40
    @22
    @24
    @38
    eqeq1
    rexbidv
    imbi2d
    syl5ibrcom
    rexlimdva
    impd
    rexlimiv
    reximi
    sylbir
    syl2anb
    vx
    vy
    vz
    vw
    vv
    vt
    @18
    @33
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
    va
    vs
    vc
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelexlem.1
    efgrelexlema
    sylibr
    adantl
    @18
    cW
    wcel
    #
    @18
    @18
    cL
    wbr
    #
    wb
    wtru
    @25
    vb
    @28
    wrex
    #
    va
    @28
    wrex
    @2
    cS
    cfv
    @18
    wceq
    #
    va
    @56
    wrex
    #
    @71
    @70
    @72
    @73
    va
    @28
    @56
    @2
    @28
    wcel
    #
    @72
    wa
    @75
    @2
    @56
    wcel
    @73
    wa
    #
    @75
    @72
    @75
    @22
    @22
    wceq
    #
    @72
    @22
    eqid
    @25
    @77
    vb
    @2
    @28
    @23
    @2
    wceq
    @24
    @22
    @22
    cc0
    @23
    @2
    fveq1
    eqeq2d
    rspcev
    mpan2
    pm4.71i
    @65
    @75
    @76
    wb
    @68
    @56
    @18
    @2
    cS
    fniniseg
    ax-mp
    bitr3i
    rexbii2
    vx
    vy
    vz
    vw
    vv
    vt
    @18
    @18
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
    va
    vb
    vc
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelexlem.1
    efgrelexlema
    @70
    @18
    cS
    crn
    #
    wcel
    #
    @74
    @78
    cW
    @18
    @66
    @78
    cW
    wceq
    @67
    @56
    cW
    cS
    forn
    ax-mp
    eleq2i
    @65
    @79
    @74
    wb
    @68
    va
    @56
    @18
    cS
    fvelrnb
    ax-mp
    bitr3i
    3bitr4ri
    a1i
    iserd
    trud
    #
    @14
    va
    cW
    @2
    cW
    wcel
    #
    vb
    @4
    @13
    @81
    @23
    @4
    wcel
    #
    @23
    @13
    wcel
    #
    @81
    @82
    wa
    #
    @2
    @23
    cL
    wbr
    #
    @83
    @84
    @44
    vs
    @16
    @23
    csn
    cima
    #
    wrex
    #
    vr
    @16
    @2
    csn
    cima
    #
    wrex
    #
    @85
    @84
    @2
    @58
    wceq
    #
    vr
    @56
    wrex
    #
    @89
    @84
    @66
    @81
    @91
    @67
    @81
    @82
    simpl
    vr
    @56
    cW
    @2
    cS
    foelrn
    sylancr
    @84
    @90
    @87
    vr
    @56
    @88
    @84
    @57
    @90
    wa
    #
    @0
    @88
    wcel
    #
    @87
    wa
    @84
    @92
    wa
    #
    @93
    @87
    @94
    @57
    @58
    @2
    wceq
    #
    @93
    @84
    @57
    @90
    simprl
    #
    @94
    @2
    @58
    @84
    @57
    @90
    simprr
    #
    eqcomd
    @65
    @93
    @57
    @95
    wa
    wb
    @68
    @56
    @2
    @0
    cS
    fniniseg
    ax-mp
    sylanbrc
    @94
    @0
    @23
    cs1
    #
    cconcat
    co
    #
    @86
    wcel
    #
    @43
    cc0
    @99
    cfv
    #
    wceq
    #
    @87
    @94
    @99
    @56
    wcel
    #
    @99
    cS
    cfv
    @23
    wceq
    #
    @100
    @94
    @57
    @23
    @58
    cT
    cfv
    #
    crn
    #
    wcel
    @103
    @96
    @94
    @23
    @4
    @106
    @81
    @82
    @92
    simplr
    @94
    @3
    @105
    @94
    @2
    @58
    cT
    @97
    fveq2d
    rneqd
    eleqtrd
    vx
    vy
    vz
    vw
    vv
    vt
    @23
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    @0
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
    @94
    @0
    cW
    cword
    #
    wcel
    #
    @23
    cW
    wcel
    #
    @103
    @104
    @94
    @0
    @108
    c0
    csn
    #
    @57
    @0
    @108
    @111
    cdif
    wcel
    #
    @84
    @90
    @57
    @112
    @43
    cD
    wcel
    @17
    @0
    cfv
    @17
    c1
    cmin
    co
    @0
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @0
    chash
    cfv
    #
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
    @0
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
    ad2antrl
    #
    eldifad
    #
    @84
    @110
    @92
    @81
    @4
    cW
    @23
    @81
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
    @81
    @3
    vf
    vg
    @116
    @117
    @2
    @18
    @18
    @19
    @19
    cM
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    wceq
    @119
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
    vf
    vg
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    simprd
    @118
    cW
    @3
    frn
    syl
    sselda
    adantr
    #
    @107
    vx
    vy
    vz
    vw
    vv
    vt
    @0
    @23
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
    @65
    @100
    @103
    @104
    wa
    wb
    @68
    @56
    @23
    @99
    cS
    fniniseg
    ax-mp
    sylanbrc
    @94
    @101
    @43
    @94
    @109
    @98
    @108
    wcel
    cc0
    cc0
    @113
    cfzo
    co
    wcel
    #
    @101
    @43
    wceq
    @115
    @94
    @23
    cW
    @120
    s1cld
    @94
    @113
    cn
    wcel
    #
    @121
    @94
    @112
    @122
    @114
    @112
    @109
    @0
    c0
    wne
    wa
    @122
    @0
    @108
    c0
    eldifsn
    cW
    @0
    lennncl
    sylbi
    syl
    @113
    lbfzo0
    sylibr
    cW
    @0
    @98
    cc0
    ccatval1
    syl3anc
    eqcomd
    @44
    @102
    vs
    @99
    @86
    @37
    @99
    wceq
    @38
    @101
    @43
    cc0
    @37
    @99
    fveq1
    eqeq2d
    rspcev
    syl2anc
    jca
    ex
    reximdv2
    mpd
    vx
    vy
    vz
    vw
    vv
    vt
    @2
    @23
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
    vr
    vs
    vc
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelexlem.1
    efgrelexlema
    sylibr
    @23
    @2
    cL
    vb
    vex
    va
    vex
    elec
    sylibr
    ex
    ssrdv
    rgen
    @8
    @12
    @15
    wa
    vr
    cL
    @12
    cW
    cvv
    wcel
    cL
    cvv
    wcel
    @80
    cW
    @117
    cword
    #
    cid
    cfv
    cvv
    efgval.w
    @123
    cid
    fvex
    eqeltri
    cW
    cL
    cvv
    erex
    mp2
    @0
    cL
    wceq
    #
    @1
    @12
    @7
    @15
    cW
    @0
    cL
    ereq1
    @124
    @6
    @14
    va
    cW
    @124
    @5
    @13
    @4
    @0
    cL
    @2
    eceq2
    sseq2d
    ralbidv
    anbi12d
    elab
    mpbir2an
    cL
    @9
    intss1
    ax-mp
    eqsstri
end
