include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wb.mm"
include "eqid.mm"
include "ltrnideq.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "bitr3d.mm"

theorem ltrn2ateq
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrn2eq.l: |- .<_ = ( le ` K )
  assume ltrn2eq.a: |- A = ( Atoms ` K )
  assume ltrn2eq.h: |- H = ( LHyp ` K )
  assume ltrn2eq.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) ) -> ( ( F ` P ) = P <-> ( F ` Q ) = Q ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    wa
    cF
    cid
    cK
    cbs
    cfv
    #
    cres
    wceq
    #
    cP
    cF
    cfv
    cP
    wceq
    #
    cQ
    cF
    cfv
    cQ
    wceq
    #
    @0
    @1
    @2
    @5
    @6
    wb
    @3
    cA
    @4
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    @4
    eqid
    #
    ltrn2eq.l
    ltrn2eq.a
    ltrn2eq.h
    ltrn2eq.t
    ltrnideq
    3adant3r3
    @0
    @1
    @3
    @5
    @7
    wb
    @2
    cA
    @4
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    @8
    ltrn2eq.l
    ltrn2eq.a
    ltrn2eq.h
    ltrn2eq.t
    ltrnideq
    3adant3r2
    bitr3d
end
