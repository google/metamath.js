include "ccnv.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "lhpocnel2.mm"
include "syl.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlval2.mm"
include "simpld.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "ltrniotacnvval.mm"
include "fveq2d.mm"
include "ltrniotaval.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "hlatjcom.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "syl6eqr.mm"

theorem dihjatcclem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let vd: setvar d
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  let c.0: class .0.
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let va: setvar a
  let vb: setvar b
  let cJ: class J
  let cN: class N
  assume dihjatcclem.b: |- B = ( Base ` K )
  assume dihjatcclem.l: |- .<_ = ( le ` K )
  assume dihjatcclem.h: |- H = ( LHyp ` K )
  assume dihjatcclem.j: |- .\/ = ( join ` K )
  assume dihjatcclem.m: |- ./\ = ( meet ` K )
  assume dihjatcclem.a: |- A = ( Atoms ` K )
  assume dihjatcclem.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatcclem.s: |- .(+) = ( LSSum ` U )
  assume dihjatcclem.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjatcclem.v: |- V = ( ( P .\/ Q ) ./\ W )
  assume dihjatcclem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjatcclem.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dihjatcclem.q: |- ( ph -> ( Q e. A /\ -. Q .<_ W ) )
  assume dihjatcc.w: |- C = ( ( oc ` K ) ` W )
  assume dihjatcc.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihjatcc.r: |- R = ( ( trL ` K ) ` W )
  assume dihjatcc.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihjatcc.g: |- G = ( iota_ d e. T ( d ` C ) = P )
  assume dihjatcc.dd: |- D = ( iota_ d e. T ( d ` C ) = Q )

  disjoint .<_ d
  disjoint A d
  disjoint B d
  disjoint C d
  disjoint H d
  disjoint P d
  disjoint K d
  disjoint Q d
  disjoint T d
  disjoint W d
  disjoint d t
  disjoint .<_ t
  disjoint f s
  disjoint .(+) f
  disjoint .(+) s
  disjoint .0. t
  disjoint g h
  disjoint g t
  disjoint g u
  disjoint D g
  disjoint h t
  disjoint h u
  disjoint D h
  disjoint t u
  disjoint D t
  disjoint D u
  disjoint a b
  disjoint a t
  disjoint E a
  disjoint b t
  disjoint E b
  disjoint E t
  disjoint d g
  disjoint H g
  disjoint H t
  disjoint J g
  disjoint J h
  disjoint J u
  disjoint N g
  disjoint N h
  disjoint N u
  disjoint f g
  disjoint f h
  disjoint f t
  disjoint f u
  disjoint I f
  disjoint g s
  disjoint I g
  disjoint h s
  disjoint I h
  disjoint s t
  disjoint s u
  disjoint I s
  disjoint I t
  disjoint I u
  disjoint d f
  disjoint d h
  disjoint d s
  disjoint d u
  disjoint P f
  disjoint P g
  disjoint P h
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint R t
  disjoint G g
  disjoint G h
  disjoint G t
  disjoint G u
  disjoint a d
  disjoint a g
  disjoint K a
  disjoint b d
  disjoint b g
  disjoint K b
  disjoint K g
  disjoint K t
  disjoint Q f
  disjoint Q g
  disjoint Q h
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint T a
  disjoint T b
  disjoint T t
  disjoint U g
  disjoint U h
  disjoint U t
  disjoint U u
  disjoint V f
  disjoint V s
  disjoint V t
  disjoint W a
  disjoint W b
  disjoint W g
  disjoint W t
  assert |- ( ph -> ( R ` ( G o. `' D ) ) = V )

  proof
    wph
    cG
    cD
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    cQ
    cQ
    @1
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cV
    wph
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    @1
    cT
    wcel
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @2
    @5
    wceq
    dihjatcclem.k
    wph
    @8
    cG
    cT
    wcel
    #
    @0
    cT
    wcel
    #
    @9
    dihjatcclem.k
    wph
    @8
    cC
    cA
    wcel
    cC
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @13
    dihjatcclem.k
    wph
    @8
    @15
    dihjatcclem.k
    cA
    cC
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.w
    lhpocnel2
    syl
    #
    dihjatcclem.p
    cA
    cC
    cP
    cT
    vd
    cG
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.g
    ltrniotacl
    syl3anc
    #
    wph
    @8
    cD
    cT
    wcel
    #
    @14
    dihjatcclem.k
    wph
    @8
    @15
    @12
    @21
    dihjatcclem.k
    @19
    dihjatcclem.q
    cA
    cC
    cQ
    cT
    vd
    cD
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.dd
    ltrniotacl
    syl3anc
    cT
    cD
    cH
    cK
    cW
    dihjatcclem.h
    dihjatcc.t
    ltrncnv
    syl2anc
    #
    cT
    cG
    @0
    cH
    cK
    cW
    dihjatcclem.h
    dihjatcc.t
    ltrnco
    syl3anc
    dihjatcclem.q
    cA
    cQ
    cR
    cT
    @1
    cH
    c.or
    cK
    c.le
    c.an
    cW
    dihjatcclem.l
    dihjatcclem.j
    dihjatcclem.m
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.r
    trlval2
    syl3anc
    wph
    @5
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    cV
    wph
    @4
    @23
    cW
    c.an
    wph
    @4
    cQ
    cP
    c.or
    co
    #
    @23
    wph
    @3
    cP
    cQ
    c.or
    wph
    @3
    cQ
    @0
    cfv
    #
    cG
    cfv
    #
    cP
    wph
    @8
    @13
    @14
    @10
    @3
    @26
    wceq
    dihjatcclem.k
    @20
    @22
    wph
    @10
    @11
    dihjatcclem.q
    simpld
    #
    cA
    cQ
    cT
    cG
    @0
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    ltrncoval
    syl121anc
    wph
    @26
    cC
    cG
    cfv
    #
    cP
    wph
    @25
    cC
    cG
    wph
    @8
    @15
    @12
    @25
    cC
    wceq
    dihjatcclem.k
    @19
    dihjatcclem.q
    cA
    cC
    cQ
    cT
    vd
    cD
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.dd
    ltrniotacnvval
    syl3anc
    fveq2d
    wph
    @8
    @15
    @18
    @28
    cP
    wceq
    dihjatcclem.k
    @19
    dihjatcclem.p
    cA
    cC
    cP
    cT
    vd
    cG
    cH
    cK
    c.le
    cW
    dihjatcclem.l
    dihjatcclem.a
    dihjatcclem.h
    dihjatcc.t
    dihjatcc.g
    ltrniotaval
    syl3anc
    eqtrd
    eqtrd
    oveq2d
    wph
    @6
    @16
    @10
    @23
    @24
    wceq
    wph
    @6
    @7
    dihjatcclem.k
    simpld
    wph
    @16
    @17
    dihjatcclem.p
    simpld
    @27
    cA
    c.or
    cK
    cP
    cQ
    dihjatcclem.j
    dihjatcclem.a
    hlatjcom
    syl3anc
    eqtr4d
    oveq1d
    dihjatcclem.v
    syl6eqr
    eqtrd
end
