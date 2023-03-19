include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp3.mm"
include "lhpmcvr2.mm"
include "syl2anc.mm"
include "clat.mm"
include "simp11l.mm"
include "adantr.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpr.mm"
include "simpl2.mm"
include "cdleme27cl.mm"
include "syl222anc.mm"
include "simpl3l.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "expr.mm"
include "adantrd.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdleme29ex
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vs: setvar s
  let vt: setvar t
  let cG: class G
  let cO: class O
  let cV: class V
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme27.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme27.z: |- Z = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme27.n: |- N = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( s .\/ z ) ./\ W ) ) )
  assume cdleme27.d: |- D = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme27.c: |- C = if ( s .<_ ( P .\/ Q ) , D , F )

  disjoint s u
  disjoint s z
  disjoint A s
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B s
  disjoint B u
  disjoint B z
  disjoint F u
  disjoint H s
  disjoint H z
  disjoint .\/ s
  disjoint .\/ u
  disjoint .\/ z
  disjoint K s
  disjoint K z
  disjoint .<_ s
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ u
  disjoint ./\ z
  disjoint N u
  disjoint P s
  disjoint P u
  disjoint P z
  disjoint Q s
  disjoint Q u
  disjoint Q z
  disjoint U s
  disjoint U u
  disjoint U z
  disjoint W s
  disjoint W u
  disjoint W z
  disjoint X s
  disjoint s t
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint B t
  disjoint G u
  disjoint H t
  disjoint .\/ t
  disjoint K t
  disjoint .<_ t
  disjoint ./\ t
  disjoint N t
  disjoint O s
  disjoint O u
  disjoint P t
  disjoint Q t
  disjoint U t
  disjoint V z
  disjoint W t
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) -> E. s e. A ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) /\ ( C .\/ ( X ./\ W ) ) e. B ) )

  proof
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
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @11
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    #
    @15
    cC
    @13
    c.or
    co
    cB
    wcel
    #
    wa
    #
    vs
    cA
    wrex
    @10
    @2
    @9
    @16
    @2
    @3
    @4
    @6
    @9
    simp11
    @5
    @6
    @9
    simp3
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    lhpmcvr2
    syl2anc
    @10
    @15
    @18
    vs
    cA
    @10
    @11
    cA
    wcel
    #
    wa
    #
    @15
    @17
    @20
    @12
    @17
    @14
    @10
    @19
    @12
    @17
    @10
    @19
    @12
    wa
    #
    wa
    #
    cK
    clat
    wcel
    #
    cC
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @17
    @22
    @0
    @23
    @10
    @0
    @21
    @0
    @1
    @3
    @4
    @6
    @9
    simp11l
    adantr
    #
    cK
    hllat
    syl
    #
    @22
    @0
    @1
    @3
    @4
    @21
    @6
    @24
    @26
    @10
    @1
    @21
    @0
    @1
    @3
    @4
    @6
    @9
    simp11r
    adantr
    #
    @2
    @3
    @4
    @6
    @9
    @21
    simpl12
    @2
    @3
    @4
    @6
    @9
    @21
    simpl13
    @10
    @21
    simpr
    @5
    @6
    @9
    @21
    simpl2
    vz
    vu
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cZ
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme27.c
    cdleme27cl
    syl222anc
    @22
    @23
    @7
    cW
    cB
    wcel
    #
    @25
    @27
    @7
    @8
    @5
    @6
    @21
    simpl3l
    @22
    @1
    @29
    @28
    cB
    cH
    cK
    cW
    cdleme26.b
    cdleme26.h
    lhpbase
    syl
    cB
    cK
    c.an
    cX
    cW
    cdleme26.b
    cdleme26.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cC
    @13
    cdleme26.b
    cdleme26.j
    latjcl
    syl3anc
    expr
    adantrd
    ancld
    reximdva
    mpd
end
