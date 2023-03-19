include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp31.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "eqid.mm"
include "cdleme41sn3a.mm"
include "syl121anc.mm"
include "simp23.mm"
include "simp32.mm"
include "cdleme35sn3a.mm"
include "nbrne2.mm"
include "syl2anc.mm"

theorem cdleme41sn3aw
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  assume cdleme41.b: |- B = ( Base ` K )
  assume cdleme41.l: |- .<_ = ( le ` K )
  assume cdleme41.j: |- .\/ = ( join ` K )
  assume cdleme41.m: |- ./\ = ( meet ` K )
  assume cdleme41.a: |- A = ( Atoms ` K )
  assume cdleme41.h: |- H = ( LHyp ` K )
  assume cdleme41.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme41.d: |- D = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme41.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme41.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme41.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = G ) )
  assume cdleme41.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint S s
  disjoint U s
  disjoint W s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint s t
  disjoint s y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint D y
  disjoint G y
  disjoint E s
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H y
  disjoint .\/ t
  disjoint .\/ y
  disjoint K s
  disjoint K t
  disjoint K y
  disjoint .<_ t
  disjoint .<_ y
  disjoint ./\ t
  disjoint ./\ y
  disjoint P t
  disjoint P y
  disjoint Q t
  disjoint Q y
  disjoint R t
  disjoint R y
  disjoint S t
  disjoint S y
  disjoint U t
  disjoint U y
  disjoint W t
  disjoint W y
  disjoint s u
  disjoint A u
  disjoint .\/ u
  disjoint .<_ u
  disjoint ./\ u
  disjoint N u
  disjoint P u
  disjoint Q u
  disjoint S u
  disjoint U u
  disjoint t u
  disjoint u y
  disjoint B u
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ R =/= S ) ) -> [_ R / s ]_ N =/= [_ S / s ]_ N )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @5
    c.le
    wbr
    wn
    #
    cR
    cS
    wne
    #
    w3a
    #
    w3a
    #
    vs
    cR
    cN
    csb
    #
    @5
    c.le
    wbr
    #
    vs
    cS
    cN
    csb
    #
    @5
    c.le
    wbr
    wn
    #
    @11
    @13
    wne
    @10
    @0
    @1
    @2
    @6
    @12
    @0
    @4
    @9
    simp1
    #
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    @0
    @1
    @2
    @3
    @9
    simp22
    @0
    @4
    @6
    @7
    @8
    simp31
    vy
    vt
    cA
    cB
    cD
    cE
    cP
    cQ
    cR
    cU
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    @5
    cE
    cR
    vt
    cv
    #
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    @17
    cW
    c.le
    wbr
    wn
    @17
    @5
    c.le
    wbr
    wn
    wa
    vy
    cv
    @18
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    #
    vs
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme41.u
    cdleme41.d
    cdleme41.e
    cdleme41.g
    cdleme41.i
    cdleme41.n
    @18
    eqid
    @19
    eqid
    cdleme41sn3a
    syl121anc
    @10
    @0
    @1
    @3
    @7
    @14
    @15
    @16
    @0
    @1
    @2
    @3
    @9
    simp23
    @0
    @4
    @6
    @7
    @8
    simp32
    cA
    cB
    cD
    cP
    cQ
    cS
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vs
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme41.u
    cdleme41.d
    cdleme41.n
    cdleme35sn3a
    syl121anc
    @11
    @13
    @5
    c.le
    nbrne2
    syl2anc
end
