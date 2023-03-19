include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp1r.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "cdlemkfid1N.mm"
include "3adant1r.mm"
include "eqtr3d.mm"
include "syl5eq.mm"

theorem cdlemkfid2N
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vb: setvar b
  assume cdlemk5.b: |- B = ( Base ` K )
  assume cdlemk5.l: |- .<_ = ( le ` K )
  assume cdlemk5.j: |- .\/ = ( join ` K )
  assume cdlemk5.m: |- ./\ = ( meet ` K )
  assume cdlemk5.a: |- A = ( Atoms ` K )
  assume cdlemk5.h: |- H = ( LHyp ` K )
  assume cdlemk5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk5.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk5.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F = N ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ b e. T ) /\ ( ( R ` b ) =/= ( R ` F ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> Z = ( b ` P ) )

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
    cN
    wceq
    #
    wa
    cF
    cT
    wcel
    cF
    cid
    cB
    cres
    wne
    vb
    cv
    #
    cT
    wcel
    w3a
    #
    @2
    cR
    cfv
    #
    cF
    cR
    cfv
    wne
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    wa
    #
    w3a
    #
    cZ
    cP
    @4
    c.or
    co
    #
    cP
    cN
    cfv
    #
    @2
    cF
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cP
    @2
    cfv
    #
    cdlemk5.z
    @6
    @7
    cP
    cF
    cfv
    #
    @9
    c.or
    co
    #
    c.an
    co
    #
    @11
    @12
    @6
    @14
    @10
    @7
    c.an
    @6
    @13
    @8
    @9
    c.or
    @6
    cP
    cF
    cN
    @0
    @1
    @3
    @5
    simp1r
    fveq1d
    oveq1d
    oveq2d
    @0
    @3
    @5
    @15
    @12
    wceq
    @1
    cA
    cB
    cP
    cR
    cT
    cF
    @2
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemkfid1N
    3adant1r
    eqtr3d
    syl5eq
end
