include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "trljat1.mm"
include "trljat2.mm"
include "eqtr4d.mm"

theorem trljat3
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trljat.l: |- .<_ = ( le ` K )
  assume trljat.j: |- .\/ = ( join ` K )
  assume trljat.a: |- A = ( Atoms ` K )
  assume trljat.h: |- H = ( LHyp ` K )
  assume trljat.t: |- T = ( ( LTrn ` K ) ` W )
  assume trljat.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( P .\/ ( R ` F ) ) = ( ( F ` P ) .\/ ( R ` F ) ) )

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
    cP
    cF
    cR
    cfv
    #
    c.or
    co
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    @1
    @0
    c.or
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
    cW
    trljat.l
    trljat.j
    trljat.a
    trljat.h
    trljat.t
    trljat.r
    trljat1
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
    trljat.l
    trljat.j
    trljat.a
    trljat.h
    trljat.t
    trljat.r
    trljat2
    eqtr4d
end
