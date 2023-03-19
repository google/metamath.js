include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "simpr.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "fveq1.mm"
include "adantl.mm"
include "impbida.mm"

theorem ltrneq3
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  assume cdlemd.l: |- .<_ = ( le ` K )
  assume cdlemd.a: |- A = ( Atoms ` K )
  assume cdlemd.h: |- H = ( LHyp ` K )
  assume cdlemd.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` P ) = ( G ` P ) <-> F = G ) )

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
    cG
    cT
    wcel
    #
    wa
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
    #
    cP
    cF
    cfv
    cP
    cG
    cfv
    wceq
    #
    cF
    cG
    wceq
    #
    @5
    @6
    wa
    @0
    @1
    @2
    @4
    @6
    @7
    @0
    @3
    @4
    @6
    simpl1
    @1
    @2
    @0
    @4
    @6
    simpl2l
    @1
    @2
    @0
    @4
    @6
    simpl2r
    @0
    @3
    @4
    @6
    simpl3
    @5
    @6
    simpr
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemd.l
    cdlemd.a
    cdlemd.h
    cdlemd.t
    cdlemd
    syl311anc
    @7
    @6
    @5
    cP
    cF
    cG
    fveq1
    adantl
    impbida
end
