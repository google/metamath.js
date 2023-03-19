include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "simp33.mm"
include "cbs.mm"
include "wceq.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp32.mm"
include "ltrn11.mm"
include "syl112anc.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem ltrn11at
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let cG: class G
  assume ltrneq2.a: |- A = ( Atoms ` K )
  assume ltrneq2.h: |- H = ( LHyp ` K )
  assume ltrneq2.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ Q e. A /\ P =/= Q ) ) -> ( F ` P ) =/= ( F ` Q ) )

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
    #
    cQ
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    #
    wne
    @4
    @0
    @1
    @2
    @3
    @4
    simp33
    @6
    @7
    @8
    cP
    cQ
    @6
    @0
    @1
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @9
    wcel
    #
    @7
    @8
    wceq
    cP
    cQ
    wceq
    wb
    @0
    @1
    @5
    simp1
    @0
    @1
    @5
    simp2
    @6
    @2
    @10
    @0
    @1
    @2
    @3
    @4
    simp31
    cA
    @9
    cP
    cK
    @9
    eqid
    #
    ltrneq2.a
    atbase
    syl
    @6
    @3
    @11
    @0
    @1
    @2
    @3
    @4
    simp32
    cA
    @9
    cQ
    cK
    @12
    ltrneq2.a
    atbase
    syl
    @9
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    cQ
    @12
    ltrneq2.h
    ltrneq2.t
    ltrn11
    syl112anc
    necon3bid
    mpbird
end
