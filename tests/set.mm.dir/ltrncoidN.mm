include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wf1o.mm"
include "simpl1.mm"
include "simpl3.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq2d.mm"
include "wf.mm"
include "simpl2.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "coass.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "coeq1d.mm"
include "fcoi2.mm"
include "eqtrd.mm"
include "f1ococnv2.mm"
include "impbida.mm"

theorem ltrncoidN
  let cB: class B
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume ltrn1o.b: |- B = ( Base ` K )
  assume ltrn1o.h: |- H = ( LHyp ` K )
  assume ltrn1o.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( ( F o. `' G ) = ( _I |` B ) <-> F = G ) )

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
    w3a
    #
    cF
    cG
    ccnv
    #
    ccom
    #
    cid
    cB
    cres
    #
    wceq
    #
    cF
    cG
    wceq
    #
    @3
    @7
    wa
    #
    cF
    @5
    cG
    ccom
    #
    cG
    @9
    cF
    cF
    @4
    cG
    ccom
    #
    ccom
    #
    @10
    @9
    @12
    cF
    @6
    ccom
    #
    cF
    @9
    @11
    @6
    cF
    @9
    cB
    cB
    cG
    wf1o
    #
    @11
    @6
    wceq
    @9
    @0
    @2
    @14
    @0
    @1
    @2
    @7
    simpl1
    #
    @0
    @1
    @2
    @7
    simpl3
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    ltrn1o.b
    ltrn1o.h
    ltrn1o.t
    ltrn1o
    #
    syl2anc
    #
    cB
    cB
    cG
    f1ococnv1
    syl
    coeq2d
    @9
    cB
    cB
    cF
    wf1o
    #
    cB
    cB
    cF
    wf
    @13
    cF
    wceq
    @9
    @0
    @1
    @18
    @15
    @0
    @1
    @2
    @7
    simpl2
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    ltrn1o.b
    ltrn1o.h
    ltrn1o.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1of
    cB
    cB
    cF
    fcoi1
    3syl
    eqtr2d
    cF
    @4
    cG
    coass
    syl6eqr
    @9
    @10
    @6
    cG
    ccom
    #
    cG
    @9
    @5
    @6
    cG
    @3
    @7
    simpr
    coeq1d
    @9
    @14
    cB
    cB
    cG
    wf
    @19
    cG
    wceq
    @17
    cB
    cB
    cG
    f1of
    cB
    cB
    cG
    fcoi2
    3syl
    eqtrd
    eqtrd
    @3
    @8
    wa
    #
    @5
    cG
    @4
    ccom
    #
    @6
    @20
    cF
    cG
    @4
    @3
    @8
    simpr
    coeq1d
    @20
    @14
    @21
    @6
    wceq
    @20
    @0
    @2
    @14
    @0
    @1
    @2
    @8
    simpl1
    @0
    @1
    @2
    @8
    simpl3
    @16
    syl2anc
    cB
    cB
    cG
    f1ococnv2
    syl
    eqtrd
    impbida
end
