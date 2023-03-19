include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "ltrnel.mm"
include "lhpmat.mm"
include "syl2anc.mm"

theorem ltrnmw
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let c.0: class .0.
  assume ltrnmw.l: |- .<_ = ( le ` K )
  assume ltrnmw.m: |- ./\ = ( meet ` K )
  assume ltrnmw.z: |- .0. = ( 0. ` K )
  assume ltrnmw.a: |- A = ( Atoms ` K )
  assume ltrnmw.h: |- H = ( LHyp ` K )
  assume ltrnmw.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` P ) ./\ W ) = .0. )

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
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    @0
    cP
    cF
    cfv
    #
    cA
    wcel
    @3
    cW
    c.le
    wbr
    wn
    wa
    @3
    cW
    c.an
    co
    c.0
    wceq
    @0
    @1
    @2
    simp1
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrnmw.l
    ltrnmw.a
    ltrnmw.h
    ltrnmw.t
    ltrnel
    cA
    @3
    cH
    cK
    c.le
    c.an
    cW
    c.0
    ltrnmw.l
    ltrnmw.m
    ltrnmw.z
    ltrnmw.a
    ltrnmw.h
    lhpmat
    syl2anc
end
