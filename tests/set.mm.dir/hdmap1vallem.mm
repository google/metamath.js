include "cfv.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "wceq.mm"
include "csn.mm"
include "c1st.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "hdmap1fval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotaex.mm"
include "ifex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem hdmap1vallem
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
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
  assume hdmap1val.t: |- ( ph -> T e. ( ( V X. D ) X. V ) )

  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint U h
  disjoint V h
  disjoint T h
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
  disjoint T x
  assert |- ( ph -> ( I ` T ) = if ( ( 2nd ` T ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` T ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` T ) ) .- ( 2nd ` T ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` T ) ) R h ) } ) ) ) ) )

  proof
    wph
    cT
    cI
    cfv
    cT
    vx
    cV
    cD
    cxp
    cV
    cxp
    #
    vx
    cv
    #
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @2
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
    @1
    c1st
    cfv
    #
    c1st
    cfv
    #
    @2
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
    @10
    c2nd
    cfv
    #
    @7
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
    #
    cmpt
    #
    cfv
    #
    cT
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @26
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @8
    wceq
    #
    cT
    c1st
    cfv
    #
    c1st
    cfv
    #
    @26
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
    @32
    c2nd
    cfv
    #
    @7
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
    #
    wph
    cT
    cI
    @24
    wph
    vx
    cA
    cC
    cD
    cQ
    cR
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
    hdmap1fval
    fveq1d
    wph
    cT
    @0
    wcel
    @45
    cvv
    wcel
    @25
    @45
    wceq
    hdmap1val.t
    @27
    cQ
    @44
    cQ
    cC
    c0g
    cfv
    cvv
    hdmap1fval.q
    cC
    c0g
    fvex
    eqeltri
    @43
    vh
    cD
    riotaex
    ifex
    vx
    cT
    @23
    @45
    @0
    cvv
    @24
    @1
    cT
    wceq
    #
    @3
    @27
    @22
    @44
    cQ
    @46
    @2
    @26
    c.0
    @1
    cT
    c2nd
    fveq2
    #
    eqeq1d
    @46
    @21
    @43
    vh
    cD
    @46
    @9
    @31
    @20
    @42
    @46
    @6
    @30
    @8
    @46
    @5
    @29
    cM
    @46
    @4
    @28
    cN
    @46
    @2
    @26
    @47
    sneqd
    fveq2d
    fveq2d
    eqeq1d
    @46
    @15
    @37
    @19
    @41
    @46
    @14
    @36
    cM
    @46
    @13
    @35
    cN
    @46
    @12
    @34
    @46
    @11
    @33
    @2
    @26
    c.mi
    @46
    @10
    @32
    c1st
    @1
    cT
    c1st
    fveq2
    #
    fveq2d
    @47
    oveq12d
    sneqd
    fveq2d
    fveq2d
    @46
    @18
    @40
    cJ
    @46
    @17
    @39
    @46
    @16
    @38
    @7
    cR
    @46
    @10
    @32
    c2nd
    @48
    fveq2d
    oveq1d
    sneqd
    fveq2d
    eqeq12d
    anbi12d
    riotabidv
    ifbieq2d
    @24
    eqid
    fvmptg
    sylancl
    eqtrd
end
