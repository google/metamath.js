include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3.mm"
include "cdlemk3.mm"
include "syl221anc.mm"
include "simp23.mm"
include "simp33l.mm"
include "simp33r.mm"
include "cdlemk4.mm"
include "syl222anc.mm"
include "eqbrtrd.mm"

theorem cdlemk5a
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T /\ X e. T ) /\ ( ( R ` G ) =/= ( R ` F ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( ( F ` P ) .\/ ( R ` F ) ) ./\ ( ( F ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) .<_ ( ( X ` P ) .\/ ( R ` ( X o. `' F ) ) ) )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cX
    cT
    wcel
    #
    w3a
    #
    cG
    cR
    cfv
    cF
    cR
    cfv
    #
    wne
    #
    cF
    cid
    cB
    cres
    #
    wne
    cG
    @9
    wne
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
    w3a
    #
    w3a
    #
    cP
    cF
    cfv
    #
    @7
    c.or
    co
    @15
    cG
    cF
    ccnv
    #
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    @15
    cP
    cX
    cfv
    cX
    @16
    ccom
    cR
    cfv
    c.or
    co
    #
    c.le
    @14
    @0
    @1
    @3
    @4
    @13
    @17
    @15
    wceq
    @0
    @1
    @6
    @13
    simp1l
    #
    @0
    @1
    @6
    @13
    simp1r
    #
    @2
    @3
    @4
    @5
    @13
    simp21
    #
    @2
    @3
    @4
    @5
    @13
    simp22
    @2
    @6
    @13
    simp3
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk3
    syl221anc
    @14
    @0
    @1
    @3
    @5
    @11
    @12
    @15
    @18
    c.le
    wbr
    @19
    @20
    @21
    @2
    @3
    @4
    @5
    @13
    simp23
    @11
    @12
    @8
    @10
    @2
    @6
    simp33l
    @11
    @12
    @8
    @10
    @2
    @6
    simp33r
    cA
    cB
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk4
    syl222anc
    eqbrtrd
end
