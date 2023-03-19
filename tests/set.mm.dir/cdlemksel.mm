include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "crio.mm"
include "simp13.mm"
include "cdlemksv.mm"
include "syl.mm"
include "eqid.mm"
include "cdlemki.mm"
include "eqeltrd.mm"

theorem cdlemksel
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )
  assume cdlemk.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )

  disjoint ./\ f
  disjoint .\/ f
  disjoint F f
  disjoint f i
  disjoint G f
  disjoint G i
  disjoint N f
  disjoint P f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ i
  disjoint A i
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint R i
  disjoint T i
  disjoint W i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` F ) ) ) -> ( S ` G ) e. T )

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
    cG
    cT
    wcel
    #
    w3a
    cN
    cT
    wcel
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    cG
    @5
    wne
    cG
    cR
    cfv
    #
    @3
    wne
    w3a
    #
    w3a
    #
    cG
    cS
    cfv
    #
    cP
    vi
    cv
    cfv
    cP
    @6
    c.or
    co
    cP
    cN
    cfv
    cG
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vi
    cT
    crio
    #
    cT
    @8
    @2
    @9
    @10
    wceq
    @0
    @1
    @2
    @4
    @7
    simp13
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk.s
    cdlemksv
    syl
    cA
    cB
    cP
    cR
    cT
    vi
    cF
    cG
    cH
    @10
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    @10
    eqid
    cdlemki
    eqeltrd
end
