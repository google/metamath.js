include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "simp111.mm"
include "simp112.mm"
include "simp113.mm"
include "simp12.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "jca.mm"
include "simp2r.mm"
include "simp3rl.mm"
include "simp13l.mm"
include "simp3lr.mm"
include "simp3rr.mm"
include "simp13r.mm"
include "3jca.mm"
include "eqid.mm"
include "cdleme21k.mm"
include "syl332anc.mm"
include "3exp.mm"
include "ralrimivv.mm"

theorem cdleme24
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  assume cdleme24.b: |- B = ( Base ` K )
  assume cdleme24.l: |- .<_ = ( le ` K )
  assume cdleme24.j: |- .\/ = ( join ` K )
  assume cdleme24.m: |- ./\ = ( meet ` K )
  assume cdleme24.a: |- A = ( Atoms ` K )
  assume cdleme24.h: |- H = ( LHyp ` K )
  assume cdleme24.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme24.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme24.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ s ) ./\ W ) ) )
  assume cdleme24.g: |- G = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme24.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ ( ( R .\/ t ) ./\ W ) ) )

  disjoint s t
  disjoint A s
  disjoint A t
  disjoint B s
  disjoint B t
  disjoint H s
  disjoint H t
  disjoint .\/ s
  disjoint .\/ t
  disjoint K s
  disjoint K t
  disjoint .<_ s
  disjoint .<_ t
  disjoint ./\ s
  disjoint P s
  disjoint P t
  disjoint Q s
  disjoint Q t
  disjoint R s
  disjoint R t
  disjoint W s
  disjoint W t
  disjoint s u
  disjoint t u
  disjoint A u
  disjoint B u
  disjoint .\/ u
  disjoint .<_ u
  disjoint ./\ u
  disjoint P u
  disjoint Q u
  disjoint R u
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) ) ) -> A. s e. A A. t e. A ( ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) /\ ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) ) -> N = O ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cP
    cQ
    wne
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
    @10
    @6
    c.le
    wbr
    wn
    #
    wa
    #
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @14
    @6
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cN
    cO
    wceq
    #
    wi
    vs
    vt
    cA
    cA
    @9
    @10
    cA
    wcel
    #
    @14
    cA
    wcel
    #
    wa
    #
    @18
    @19
    @9
    @22
    @18
    w3a
    #
    @0
    @1
    @2
    @4
    @20
    @11
    wa
    @21
    @15
    wa
    @5
    @12
    @16
    @7
    w3a
    @19
    @0
    @1
    @2
    @4
    @8
    @22
    @18
    simp111
    @0
    @1
    @2
    @4
    @8
    @22
    @18
    simp112
    @0
    @1
    @2
    @4
    @8
    @22
    @18
    simp113
    @3
    @4
    @8
    @22
    @18
    simp12
    @23
    @20
    @11
    @9
    @20
    @21
    @18
    simp2l
    @11
    @12
    @17
    @9
    @22
    simp3ll
    jca
    @23
    @21
    @15
    @9
    @20
    @21
    @18
    simp2r
    @15
    @16
    @13
    @9
    @22
    simp3rl
    jca
    @5
    @7
    @3
    @4
    @22
    @18
    simp13l
    @23
    @12
    @16
    @7
    @11
    @12
    @17
    @9
    @22
    simp3lr
    @15
    @16
    @13
    @9
    @22
    simp3rr
    @5
    @7
    @3
    @4
    @22
    @18
    simp13r
    3jca
    cA
    cR
    @10
    c.or
    co
    cW
    c.an
    co
    #
    cP
    cQ
    cR
    @10
    @14
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cR
    @14
    c.or
    co
    cW
    c.an
    co
    #
    cdleme24.l
    cdleme24.j
    cdleme24.m
    cdleme24.a
    cdleme24.h
    cdleme24.u
    cdleme24.f
    cdleme24.g
    @24
    eqid
    @25
    eqid
    cdleme24.n
    cdleme24.o
    cdleme21k
    syl332anc
    3exp
    ralrimivv
end
