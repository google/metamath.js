include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cdleme8.mm"
include "eqcomd.mm"

theorem cdlemg3a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg3.l: |- .<_ = ( le ` K )
  assume cdlemg3.j: |- .\/ = ( join ` K )
  assume cdlemg3.m: |- ./\ = ( meet ` K )
  assume cdlemg3.a: |- A = ( Atoms ` K )
  assume cdlemg3.h: |- H = ( LHyp ` K )
  assume cdlemg3.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) -> ( P .\/ Q ) = ( P .\/ U ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    w3a
    cP
    cU
    c.or
    co
    cP
    cQ
    c.or
    co
    cA
    cU
    cP
    cQ
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg3.l
    cdlemg3.j
    cdlemg3.m
    cdlemg3.a
    cdlemg3.h
    cdlemg3.u
    cdleme8
    eqcomd
end
