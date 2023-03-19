include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp3l.mm"
include "simp3rr.mm"
include "simp2.mm"
include "cdlemefr27cl.mm"
include "syl33anc.mm"
include "cdlemefr32snb.mm"
include "cdlemefrs32fva.mm"

theorem cdlemefr32fvaN
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let vs: setvar s
  assume cdlemefr27.b: |- B = ( Base ` K )
  assume cdlemefr27.l: |- .<_ = ( le ` K )
  assume cdlemefr27.j: |- .\/ = ( join ` K )
  assume cdlemefr27.m: |- ./\ = ( meet ` K )
  assume cdlemefr27.a: |- A = ( Atoms ` K )
  assume cdlemefr27.h: |- H = ( LHyp ` K )
  assume cdlemefr27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefr27.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdlemefr27.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme29fr.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  disjoint s z
  disjoint H s
  disjoint K s
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint s x
  disjoint B s
  disjoint B x
  disjoint B z
  disjoint H z
  disjoint .\/ x
  disjoint .\/ z
  disjoint K z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R x
  disjoint R z
  disjoint W x
  disjoint W z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> [_ R / x ]_ O = [_ R / s ]_ N )

  proof
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cR
    @1
    c.le
    wbr
    #
    wn
    vx
    vz
    cA
    cB
    cP
    cQ
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    vs
    cdlemefr27.b
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    @0
    cR
    wceq
    @2
    @4
    @0
    cR
    @1
    c.le
    breq1
    notbid
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
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
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
    w3a
    #
    cP
    cQ
    wne
    #
    @0
    cA
    wcel
    #
    @0
    cW
    c.le
    wbr
    wn
    #
    @3
    wa
    #
    wa
    #
    w3a
    @5
    @6
    @9
    @14
    @3
    @13
    cN
    cB
    wcel
    @5
    @8
    @11
    @13
    @17
    simp11
    @6
    @7
    @5
    @11
    @13
    @17
    simp12l
    @9
    @10
    @5
    @8
    @13
    @17
    simp13l
    @12
    @13
    @14
    @16
    simp3l
    @15
    @3
    @14
    @12
    @13
    simp3rr
    @12
    @13
    @17
    simp2
    cA
    cB
    cC
    cP
    cQ
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
    cdlemefr27.b
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    cdlemefr27.u
    cdlemefr27.c
    cdlemefr27.n
    cdlemefr27cl
    syl33anc
    cA
    cB
    cC
    cP
    cQ
    cR
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
    cdlemefr27.b
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    cdlemefr27.u
    cdlemefr27.c
    cdlemefr27.n
    cdlemefr32snb
    cdleme29fr.o
    cdlemefrs32fva
end
