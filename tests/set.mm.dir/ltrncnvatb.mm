include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccnv.mm"
include "cfv.mm"
include "wb.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "f1ocnvdm.mm"
include "stoic3.mm"
include "ltrnatb.mm"
include "syld3an3.mm"
include "wceq.mm"
include "f1ocnvfv2.mm"
include "eleq1d.mm"
include "bitr2d.mm"

theorem ltrncnvatb
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume ltrnatb.b: |- B = ( Base ` K )
  assume ltrnatb.a: |- A = ( Atoms ` K )
  assume ltrnatb.h: |- H = ( LHyp ` K )
  assume ltrnatb.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ P e. B ) -> ( P e. A <-> ( `' F ` P ) e. A ) )

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
    cB
    wcel
    #
    w3a
    #
    cP
    cF
    ccnv
    cfv
    #
    cA
    wcel
    #
    @4
    cF
    cfv
    #
    cA
    wcel
    #
    cP
    cA
    wcel
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @5
    @7
    wb
    @0
    @1
    cB
    cB
    cF
    wf1o
    #
    @2
    @8
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    ltrnatb.b
    ltrnatb.h
    ltrnatb.t
    ltrn1o
    #
    cB
    cB
    cP
    cF
    f1ocnvdm
    stoic3
    cA
    cB
    @4
    cT
    cF
    cH
    cK
    cW
    ltrnatb.b
    ltrnatb.a
    ltrnatb.h
    ltrnatb.t
    ltrnatb
    syld3an3
    @3
    @6
    cP
    cA
    @0
    @1
    @9
    @2
    @6
    cP
    wceq
    @10
    cB
    cB
    cP
    cF
    f1ocnvfv2
    stoic3
    eleq1d
    bitr2d
end
