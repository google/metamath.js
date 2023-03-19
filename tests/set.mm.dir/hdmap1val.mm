include "cotp.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "c1st.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cop.mm"
include "cxp.mm"
include "df-ot.mm"
include "wcel.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"
include "hdmap1vallem.mm"
include "ot3rdg.mm"
include "syl.mm"
include "eqeq1d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "ot1stg.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "ot2ndg.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "ifbieq2d.mm"
include "eqtrd.mm"

theorem hdmap1val
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let cT: class T
  assume hdmap1val.h: |- H = ( LHyp ` K )
  assume hdmap1fval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1fval.v: |- V = ( Base ` U )
  assume hdmap1fval.s: |- .- = ( -g ` U )
  assume hdmap1fval.o: |- .0. = ( 0g ` U )
  assume hdmap1fval.n: |- N = ( LSpan ` U )
  assume hdmap1fval.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1fval.d: |- D = ( Base ` C )
  assume hdmap1fval.r: |- R = ( -g ` C )
  assume hdmap1fval.q: |- Q = ( 0g ` C )
  assume hdmap1fval.j: |- J = ( LSpan ` C )
  assume hdmap1fval.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1fval.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1fval.k: |- ( ph -> ( K e. A /\ W e. H ) )
  assume hdmap1val.x: |- ( ph -> X e. V )
  assume hdmap1val.f: |- ( ph -> F e. D )
  assume hdmap1val.y: |- ( ph -> Y e. V )

  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint U h
  disjoint V h
  disjoint F h
  disjoint X h
  disjoint Y h
  disjoint h ph
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint a c
  disjoint a d
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint K a
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint K c
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint K d
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint K j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint K k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint K m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint K n
  disjoint u v
  disjoint u w
  disjoint K u
  disjoint v w
  disjoint K v
  disjoint K w
  disjoint a h
  disjoint a x
  disjoint c h
  disjoint c x
  disjoint d h
  disjoint d x
  disjoint h j
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint j x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint C x
  disjoint D a
  disjoint D c
  disjoint D d
  disjoint D j
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint J a
  disjoint J c
  disjoint J d
  disjoint J j
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint M a
  disjoint M c
  disjoint M d
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint N a
  disjoint N n
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint .0. a
  disjoint .0. n
  disjoint .0. u
  disjoint .0. v
  disjoint .0. w
  disjoint Q a
  disjoint Q c
  disjoint Q d
  disjoint Q j
  disjoint Q n
  disjoint Q u
  disjoint Q v
  disjoint Q w
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R j
  disjoint R n
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint .- a
  disjoint .- n
  disjoint .- u
  disjoint .- v
  disjoint .- w
  disjoint U x
  disjoint V a
  disjoint V n
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint W a
  disjoint W c
  disjoint W d
  disjoint W j
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint T h
  disjoint T x
  assert |- ( ph -> ( I ` <. X , F , Y >. ) = if ( Y = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( F R h ) } ) ) ) ) )

  proof
    wph
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    @0
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @1
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    vh
    cv
    #
    csn
    cJ
    cfv
    #
    wceq
    #
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    @1
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @9
    c2nd
    cfv
    #
    @6
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    cY
    c.0
    wceq
    #
    cQ
    cY
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @7
    wceq
    #
    cX
    cY
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    cF
    @6
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    wph
    cA
    cC
    cD
    cQ
    cR
    @0
    cU
    vh
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    c.0
    hdmap1val.h
    hdmap1fval.u
    hdmap1fval.v
    hdmap1fval.s
    hdmap1fval.o
    hdmap1fval.n
    hdmap1fval.c
    hdmap1fval.d
    hdmap1fval.r
    hdmap1fval.q
    hdmap1fval.j
    hdmap1fval.m
    hdmap1fval.i
    hdmap1fval.k
    wph
    @0
    cX
    cF
    cop
    #
    cY
    cop
    #
    cV
    cD
    cxp
    #
    cV
    cxp
    #
    cX
    cF
    cY
    df-ot
    wph
    @37
    @39
    wcel
    #
    cY
    cV
    wcel
    #
    @38
    @40
    wcel
    wph
    cX
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    @41
    hdmap1val.x
    hdmap1val.f
    cX
    cF
    cV
    cD
    opelxp
    sylanbrc
    hdmap1val.y
    @37
    cY
    @39
    cV
    opelxp
    sylanbrc
    syl5eqel
    hdmap1vallem
    wph
    @2
    @22
    @21
    @36
    cQ
    wph
    @1
    cY
    c.0
    wph
    @42
    @1
    cY
    wceq
    hdmap1val.y
    cX
    cF
    cY
    cV
    ot3rdg
    syl
    #
    eqeq1d
    wph
    @20
    @35
    vh
    cD
    wph
    @8
    @26
    @19
    @34
    wph
    @5
    @25
    @7
    wph
    @4
    @24
    cM
    wph
    @3
    @23
    cN
    wph
    @1
    cY
    @45
    sneqd
    fveq2d
    fveq2d
    eqeq1d
    wph
    @14
    @30
    @18
    @33
    wph
    @13
    @29
    cM
    wph
    @12
    @28
    cN
    wph
    @11
    @27
    wph
    @10
    cX
    @1
    cY
    c.mi
    wph
    @43
    @44
    @42
    @10
    cX
    wceq
    hdmap1val.x
    hdmap1val.f
    hdmap1val.y
    cX
    cF
    cY
    cV
    cD
    cV
    ot1stg
    syl3anc
    @45
    oveq12d
    sneqd
    fveq2d
    fveq2d
    wph
    @17
    @32
    cJ
    wph
    @16
    @31
    wph
    @15
    cF
    @6
    cR
    wph
    @43
    @44
    @42
    @15
    cF
    wceq
    hdmap1val.x
    hdmap1val.f
    hdmap1val.y
    cX
    cF
    cY
    cV
    cD
    cV
    ot2ndg
    syl3anc
    oveq1d
    sneqd
    fveq2d
    eqeq12d
    anbi12d
    riotabidv
    ifbieq2d
    eqtrd
end
