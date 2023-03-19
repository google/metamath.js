include "cdlemg25zz.mm"

theorem cdlemg26zz
  let vz: setvar z
  let cA: class A
  let cQ: class Q
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
  let vr: setvar r
  let cP: class P
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( z e. A /\ -. z .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. ( R ` F ) .<_ ( Q .\/ z ) /\ -. ( R ` G ) .<_ ( Q .\/ z ) ) ) -> ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) = ( ( z .\/ ( F ` ( G ` z ) ) ) ./\ W ) )

  proof
    vz
    cA
    cQ
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg25zz
end
