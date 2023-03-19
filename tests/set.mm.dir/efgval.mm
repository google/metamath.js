include "cefg.mm"
include "cfv.mm"
include "cv.mm"
include "wer.mm"
include "cop.mm"
include "c1o.mm"
include "cdif.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "wbr.mm"
include "c2o.mm"
include "wral.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cxp.mm"
include "cword.mm"
include "wb.mm"
include "cid.mm"
include "vex.mm"
include "con0.mm"
include "2on.mm"
include "elexi.mm"
include "xpex.mm"
include "wrdexg.mm"
include "fvi.mm"
include "mp2b.mm"
include "xpeq1.mm"
include "wrdeq.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "syl6eqr.mm"
include "ereq2.mm"
include "raleq.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "inteqd.mm"
include "df-efg.mm"
include "wex.mm"
include "efglem.mm"
include "intexab.mm"
include "mpbi.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wss.mm"
include "cuni.mm"
include "wne.mm"
include "abn0.mm"
include "mpbir.mm"
include "intssuni.mm"
include "ax-mp.mm"
include "wi.mm"
include "wal.mm"
include "erssxp.mm"
include "efgrcl.mm"
include "simpld.mm"
include "con3i.mm"
include "eq0rdv.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "ss0b.mm"
include "sylibr.mm"
include "sylan9ssr.mm"
include "ex.mm"
include "adantrd.mm"
include "alrimiv.mm"
include "sseq1.mm"
include "ralab2.mm"
include "unissb.mm"
include "syl5ss.mm"
include "ss0.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem efgval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.sm: class .~
  let vn: setvar n
  let cI: class I
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let cA: class A
  let cJ: class J
  let cL: class L
  let cF: class F
  let cK: class K
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let cP: class P
  let wph: wff ph
  let vm: setvar m
  let cM: class M
  let cN: class N
  let cU: class U
  let vk: setvar k
  let vo: setvar o
  let cT: class T
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )

  disjoint r y
  disjoint r z
  disjoint y z
  disjoint n y
  disjoint n z
  disjoint n r
  disjoint n x
  disjoint r x
  disjoint W n
  disjoint W r
  disjoint x y
  disjoint x z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint .~ r
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint I n
  disjoint I r
  disjoint I x
  disjoint I y
  disjoint I z
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
  disjoint n t
  disjoint n v
  disjoint n w
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
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint M m
  disjoint n s
  disjoint n u
  disjoint M n
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint M r
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint M s
  disjoint t u
  disjoint t x
  disjoint M t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint M u
  disjoint v x
  disjoint M v
  disjoint w x
  disjoint M w
  disjoint M x
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
  disjoint k m
  disjoint k o
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint T k
  disjoint m o
  disjoint T m
  disjoint o r
  disjoint o s
  disjoint o t
  disjoint o u
  disjoint o x
  disjoint T o
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T x
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
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint W k
  disjoint m y
  disjoint m z
  disjoint W m
  disjoint n o
  disjoint o v
  disjoint o w
  disjoint o y
  disjoint o z
  disjoint W o
  disjoint s y
  disjoint s z
  disjoint W s
  disjoint W t
  disjoint u y
  disjoint u z
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint .~ a
  disjoint .~ b
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ i
  disjoint .~ j
  disjoint .~ m
  disjoint .~ s
  disjoint .~ t
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
  disjoint I m
  disjoint I s
  disjoint I t
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D m
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  assert |- .~ = |^| { r | ( r Er W /\ A. x e. W A. n e. ( 0 ... ( # ` x ) ) A. y e. I A. z e. 2o x r ( x splice <. n , n , <" <. y , z >. <. y , ( 1o \ z ) >. "> >. ) ) }

  proof
    c.sm
    cI
    cefg
    cfv
    #
    cW
    vr
    cv
    #
    wer
    #
    vx
    cv
    #
    @3
    vn
    cv
    #
    @4
    vy
    cv
    #
    vz
    cv
    #
    cop
    @5
    c1o
    @6
    cdif
    cop
    cs2
    cotp
    csplice
    co
    @1
    wbr
    vz
    c2o
    wral
    #
    vy
    cI
    wral
    #
    vn
    cc0
    @3
    chash
    cfv
    cfz
    co
    #
    wral
    #
    vx
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
    efgval.r
    cI
    cvv
    wcel
    #
    @0
    @14
    wceq
    vi
    cI
    vi
    cv
    #
    c2o
    cxp
    #
    cword
    #
    @1
    wer
    #
    @7
    vy
    @16
    wral
    #
    vn
    @9
    wral
    #
    vx
    @18
    wral
    #
    wa
    #
    vr
    cab
    #
    cint
    @14
    cvv
    cefg
    @16
    cI
    wceq
    #
    @24
    @13
    @25
    @23
    @12
    vr
    @25
    @19
    @2
    @22
    @11
    @25
    @18
    cW
    wceq
    @19
    @2
    wb
    @25
    @18
    cI
    c2o
    cxp
    #
    cword
    #
    cid
    cfv
    #
    cW
    @25
    @18
    @18
    cid
    cfv
    #
    @28
    @17
    cvv
    wcel
    @18
    cvv
    wcel
    @29
    @18
    wceq
    @16
    c2o
    vi
    vex
    c2o
    con0
    2on
    elexi
    xpex
    @17
    cvv
    wrdexg
    @18
    cvv
    fvi
    mp2b
    @25
    @18
    @27
    cid
    @25
    @17
    @26
    wceq
    @18
    @27
    wceq
    @16
    cI
    c2o
    xpeq1
    @17
    @26
    wrdeq
    syl
    fveq2d
    syl5eqr
    efgval.w
    syl6eqr
    #
    @18
    cW
    @1
    ereq2
    syl
    @25
    @21
    @10
    vx
    @18
    cW
    @30
    @25
    @20
    @8
    vn
    @9
    @7
    vy
    @16
    cI
    raleq
    ralbidv
    raleqbidv
    anbi12d
    abbidv
    inteqd
    vx
    vy
    vz
    vi
    vn
    vr
    df-efg
    @12
    vr
    wex
    #
    @14
    cvv
    wcel
    vx
    vy
    vz
    vn
    cI
    cW
    vr
    efgval.w
    efglem
    #
    @12
    vr
    intexab
    mpbi
    fvmpt
    @15
    wn
    #
    @0
    c0
    @14
    cI
    cefg
    fvprc
    @33
    @14
    c0
    wss
    @14
    c0
    wceq
    @33
    @14
    @13
    cuni
    #
    c0
    @13
    c0
    wne
    #
    @14
    @34
    wss
    @35
    @31
    @32
    @12
    vr
    abn0
    mpbir
    @13
    intssuni
    ax-mp
    @33
    vw
    cv
    #
    c0
    wss
    #
    vw
    @13
    wral
    #
    @34
    c0
    wss
    @33
    @12
    @1
    c0
    wss
    #
    wi
    #
    vr
    wal
    @38
    @33
    @40
    vr
    @33
    @2
    @39
    @11
    @33
    @2
    @39
    @2
    @33
    @1
    cW
    cW
    cxp
    #
    c0
    cW
    @1
    erssxp
    @33
    @41
    c0
    wceq
    @41
    c0
    wss
    @33
    @41
    cW
    c0
    cxp
    c0
    @33
    cW
    c0
    cW
    @33
    vx
    cW
    @3
    cW
    wcel
    #
    @15
    @42
    @15
    cW
    @27
    wceq
    @3
    cI
    cW
    efgval.w
    efgrcl
    simpld
    con3i
    eq0rdv
    xpeq2d
    cW
    xp0
    syl6eq
    @41
    ss0b
    sylibr
    sylan9ssr
    ex
    adantrd
    alrimiv
    @12
    @37
    @39
    vw
    vr
    @36
    @1
    c0
    sseq1
    ralab2
    sylibr
    vw
    @13
    c0
    unissb
    sylibr
    syl5ss
    @14
    ss0
    syl
    eqtr4d
    pm2.61i
    eqtri
end
