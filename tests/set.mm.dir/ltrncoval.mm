include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "ccom.mm"
include "wceq.mm"
include "wf1o.mm"
include "simp1.mm"
include "simp2r.mm"
include "eqid.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "fvco3.mm"

theorem ltrncoval
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnel.l: |- .<_ = ( le ` K )
  assume ltrnel.a: |- A = ( Atoms ` K )
  assume ltrnel.h: |- H = ( LHyp ` K )
  assume ltrnel.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ P e. A ) -> ( ( F o. G ) ` P ) = ( F ` ( G ` P ) ) )

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
    #
    w3a
    #
    cK
    cbs
    cfv
    #
    @6
    cG
    wf
    #
    cP
    @6
    wcel
    #
    cP
    cF
    cG
    ccom
    cfv
    cP
    cG
    cfv
    cF
    cfv
    wceq
    @5
    @6
    @6
    cG
    wf1o
    #
    @7
    @5
    @0
    @2
    @9
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2r
    @6
    cT
    cG
    cH
    cK
    chlt
    cW
    @6
    eqid
    #
    ltrnel.h
    ltrnel.t
    ltrn1o
    syl2anc
    @6
    @6
    cG
    f1of
    syl
    @4
    @0
    @8
    @3
    cA
    @6
    cP
    cK
    @10
    ltrnel.a
    atbase
    3ad2ant3
    @6
    @6
    cP
    cF
    cG
    fvco3
    syl2anc
end
