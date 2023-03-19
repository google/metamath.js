include "co.mm"
include "eqid.mm"
include "cdlemg2m.mm"

theorem cdlemg10b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( ( ( F ` P ) .\/ ( F ` Q ) ) ./\ W ) = ( ( P .\/ Q ) ./\ W ) )

  proof
    cA
    cP
    cQ
    cT
    cP
    cQ
    c.or
    co
    cW
    c.an
    co
    #
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.h
    cdlemg8.t
    cdlemg8.l
    cdlemg8.j
    cdlemg8.a
    cdlemg8.m
    @0
    eqid
    cdlemg2m
end
