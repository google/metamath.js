include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "ccom.mm"
include "wf.mm"
include "wf1o.mm"
include "simp1.mm"
include "simp2r.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "fcoi1.mm"
include "simp3.mm"
include "coeq2d.mm"
include "coeq1d.mm"
include "fcoi2.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"

theorem cdlemg47a
  let cB: class B
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume cdlemg46.b: |- B = ( Base ` K )
  assume cdlemg46.h: |- H = ( LHyp ` K )
  assume cdlemg46.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ F = ( _I |` B ) ) -> ( F o. G ) = ( G o. F ) )

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
    cF
    cid
    cB
    cres
    #
    wceq
    #
    w3a
    #
    cG
    @4
    ccom
    #
    cG
    cG
    cF
    ccom
    cF
    cG
    ccom
    #
    @6
    cB
    cB
    cG
    wf
    #
    @7
    cG
    wceq
    @6
    cB
    cB
    cG
    wf1o
    #
    @9
    @6
    @0
    @2
    @10
    @0
    @3
    @5
    simp1
    @0
    @1
    @2
    @5
    simp2r
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    ltrn1o
    syl2anc
    cB
    cB
    cG
    f1of
    syl
    #
    cB
    cB
    cG
    fcoi1
    syl
    @6
    cF
    @4
    cG
    @0
    @3
    @5
    simp3
    #
    coeq2d
    @6
    @8
    @4
    cG
    ccom
    #
    cG
    @6
    cF
    @4
    cG
    @12
    coeq1d
    @6
    @9
    @13
    cG
    wceq
    @11
    cB
    cB
    cG
    fcoi2
    syl
    eqtrd
    3eqtr4rd
end
