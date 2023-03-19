include "cv.mm"
include "cdlemg4.mm"

theorem cdlemg6b
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
  let cV: class V
  let cW: class W
  let vr: setvar r
  let cP: class P
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )

  disjoint A r
  disjoint F r
  disjoint G r
  disjoint H r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint Q r
  disjoint T r
  disjoint V r
  disjoint W r
  disjoint P r
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( r e. A /\ -. r .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. Q .<_ ( r .\/ V ) /\ ( F ` ( G ` r ) ) = r ) ) -> ( F ` ( G ` Q ) ) = Q )

  proof
    cA
    vr
    cv
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cV
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg4
end
