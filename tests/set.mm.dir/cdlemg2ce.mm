include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wrex.mm"
include "simp2.mm"
include "wb.mm"
include "cdlemg2cex.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp31.mm"
include "jca.mm"
include "simp2r.mm"
include "simp32.mm"
include "simp13.mm"
include "syl31anc.mm"
include "simp33.mm"
include "syl.mm"
include "mpbird.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem cdlemg2ce
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  let vq: setvar q
  let vp: setvar p
  let vf: setvar f
  let cP: class P
  let cQ: class Q
  let cX: class X
  assume cdlemg2.b: |- B = ( Base ` K )
  assume cdlemg2.l: |- .<_ = ( le ` K )
  assume cdlemg2.j: |- .\/ = ( join ` K )
  assume cdlemg2.m: |- ./\ = ( meet ` K )
  assume cdlemg2.a: |- A = ( Atoms ` K )
  assume cdlemg2.h: |- H = ( LHyp ` K )
  assume cdlemg2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2ex.u: |- U = ( ( p .\/ q ) ./\ W )
  assume cdlemg2ex.d: |- D = ( ( t .\/ U ) ./\ ( q .\/ ( ( p .\/ t ) ./\ W ) ) )
  assume cdlemg2ex.e: |- E = ( ( p .\/ q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemg2ex.g: |- G = ( x e. B |-> if ( ( p =/= q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( p .\/ q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( p .\/ q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )
  assume cdlemg2ce.p: |- ( F = G -> ( ps <-> ch ) )
  assume cdlemg2ce.c: |- ( ( ( ( K e. HL /\ W e. H ) /\ ( p e. A /\ -. p .<_ W ) /\ ( q e. A /\ -. q .<_ W ) ) /\ ph ) -> ch )

  disjoint p q
  disjoint p ph
  disjoint ph q
  disjoint p ps
  disjoint ps q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint F p
  disjoint F q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint T p
  disjoint T q
  disjoint W p
  disjoint W q
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint D f
  disjoint E f
  disjoint .\/ f
  disjoint ./\ f
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint F f
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  disjoint G f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ph ) -> ps )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    wph
    w3a
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cF
    cG
    wceq
    #
    w3a
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    #
    wps
    @2
    @1
    @9
    @0
    @1
    wph
    simp2
    @0
    @1
    @1
    @9
    wb
    wph
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cT
    cU
    cE
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    vq
    vp
    cdlemg2.b
    cdlemg2.l
    cdlemg2.j
    cdlemg2.m
    cdlemg2.a
    cdlemg2.h
    cdlemg2.t
    cdlemg2ex.u
    cdlemg2ex.d
    cdlemg2ex.e
    cdlemg2ex.g
    cdlemg2cex
    3ad2ant1
    mpbid
    @2
    @8
    wps
    vp
    vq
    cA
    cA
    @2
    @3
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    @8
    wps
    @2
    @12
    @8
    w3a
    #
    wps
    wch
    @13
    @0
    @10
    @4
    wa
    @11
    @6
    wa
    wph
    wch
    @0
    @1
    wph
    @12
    @8
    simp11
    @13
    @10
    @4
    @2
    @10
    @11
    @8
    simp2l
    @2
    @12
    @4
    @6
    @7
    simp31
    jca
    @13
    @11
    @6
    @2
    @10
    @11
    @8
    simp2r
    @2
    @12
    @4
    @6
    @7
    simp32
    jca
    @0
    @1
    wph
    @12
    @8
    simp13
    cdlemg2ce.c
    syl31anc
    @13
    @7
    wps
    wch
    wb
    @2
    @12
    @4
    @6
    @7
    simp33
    cdlemg2ce.p
    syl
    mpbird
    3exp
    rexlimdvv
    mpd
end
