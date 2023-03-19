include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "trlval2.mm"
include "trljat1.mm"
include "oveq1d.mm"
include "eqtr4d.mm"

theorem trlval5
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume trlval3.l: |- .<_ = ( le ` K )
  assume trlval3.j: |- .\/ = ( join ` K )
  assume trlval3.m: |- ./\ = ( meet ` K )
  assume trlval3.a: |- A = ( Atoms ` K )
  assume trlval3.h: |- H = ( LHyp ` K )
  assume trlval3.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlval3.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( R ` F ) = ( ( P .\/ ( R ` F ) ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
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
    w3a
    #
    cF
    cR
    cfv
    #
    cP
    cP
    cF
    cfv
    c.or
    co
    #
    cW
    c.an
    co
    cP
    @1
    c.or
    co
    #
    cW
    c.an
    co
    cA
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
    trlval3.l
    trlval3.j
    trlval3.m
    trlval3.a
    trlval3.h
    trlval3.t
    trlval3.r
    trlval2
    @0
    @3
    @2
    cW
    c.an
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    cW
    trlval3.l
    trlval3.j
    trlval3.a
    trlval3.h
    trlval3.t
    trlval3.r
    trljat1
    oveq1d
    eqtr4d
end
