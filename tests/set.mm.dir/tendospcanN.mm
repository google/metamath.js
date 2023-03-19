include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "tendocnv.mm"
include "3adant3l.mm"
include "coeq2d.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "tendospdi1.mm"
include "syl13anc.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simpl3r.mm"
include "ltrncoidN.mm"
include "ltrnco.mm"
include "simpr.mm"
include "tendoid0.mm"
include "syl112anc.mm"
include "3bitr3d.mm"
include "biimpd.mm"
include "impancom.mm"
include "necon1d.mm"
include "sylibd.mm"
include "3exp1.mm"
include "com24.mm"
include "imp5a.mm"
include "3imp.mm"
include "fveq2.mm"
include "impbid1.mm"

theorem tendospcanN
  let cB: class B
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  assume tendospcan.b: |- B = ( Base ` K )
  assume tendospcan.h: |- H = ( LHyp ` K )
  assume tendospcan.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendospcan.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendospcan.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint T f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S e. E /\ S =/= O ) /\ ( F e. T /\ G e. T ) ) -> ( ( S ` F ) = ( S ` G ) <-> F = G ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    #
    cS
    cO
    wne
    #
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
    w3a
    cF
    cS
    cfv
    #
    cG
    cS
    cfv
    #
    wceq
    #
    cF
    cG
    wceq
    #
    @0
    @3
    @6
    @9
    @10
    wi
    @0
    @9
    @6
    @3
    @10
    @0
    @9
    @6
    @1
    @2
    @10
    @0
    @1
    @6
    @9
    @2
    @10
    wi
    #
    @0
    @1
    @6
    @9
    @11
    @0
    @1
    @6
    w3a
    #
    @9
    wa
    #
    @2
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
    @10
    @13
    @15
    @16
    cS
    cO
    @12
    @15
    @16
    wne
    #
    @9
    cS
    cO
    wceq
    #
    @12
    @18
    wa
    #
    @9
    @19
    @20
    @7
    @8
    ccnv
    #
    ccom
    #
    @16
    wceq
    #
    @15
    cS
    cfv
    #
    @16
    wceq
    #
    @9
    @19
    @20
    @22
    @24
    @16
    @12
    @22
    @24
    wceq
    @18
    @12
    @22
    @7
    @14
    cS
    cfv
    #
    ccom
    #
    @24
    @12
    @21
    @26
    @7
    @0
    @1
    @5
    @21
    @26
    wceq
    @4
    cS
    cT
    cE
    cG
    cH
    cK
    cW
    tendospcan.h
    tendospcan.t
    tendospcan.e
    tendocnv
    3adant3l
    coeq2d
    @12
    @0
    @1
    @4
    @14
    cT
    wcel
    #
    @24
    @27
    wceq
    @0
    @1
    @6
    simp1
    #
    @0
    @1
    @6
    simp2
    @0
    @1
    @4
    @5
    simp3l
    @12
    @0
    @5
    @28
    @29
    @0
    @1
    @4
    @5
    simp3r
    cT
    cG
    cH
    cK
    cW
    tendospcan.h
    tendospcan.t
    ltrncnv
    #
    syl2anc
    cT
    cS
    cE
    cF
    @14
    cH
    cK
    chlt
    cW
    tendospcan.h
    tendospcan.t
    tendospcan.e
    tendospdi1
    syl13anc
    eqtr4d
    adantr
    eqeq1d
    @20
    @0
    @7
    cT
    wcel
    #
    @8
    cT
    wcel
    #
    @23
    @9
    wb
    @0
    @1
    @6
    @18
    simpl1
    #
    @20
    @0
    @1
    @4
    @31
    @33
    @0
    @1
    @6
    @18
    simpl2
    #
    @4
    @5
    @0
    @1
    @18
    simpl3l
    #
    cS
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendospcan.h
    tendospcan.t
    tendospcan.e
    tendocl
    syl3anc
    @20
    @0
    @1
    @5
    @32
    @33
    @34
    @4
    @5
    @0
    @1
    @18
    simpl3r
    #
    cS
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    tendospcan.h
    tendospcan.t
    tendospcan.e
    tendocl
    syl3anc
    cB
    cT
    @7
    @8
    cH
    cK
    cW
    tendospcan.b
    tendospcan.h
    tendospcan.t
    ltrncoidN
    syl3anc
    @20
    @0
    @1
    @15
    cT
    wcel
    #
    @18
    @25
    @19
    wb
    @33
    @34
    @20
    @0
    @4
    @28
    @37
    @33
    @35
    @20
    @0
    @5
    @28
    @33
    @36
    @30
    syl2anc
    cT
    cF
    @14
    cH
    cK
    cW
    tendospcan.h
    tendospcan.t
    ltrnco
    syl3anc
    @12
    @18
    simpr
    cB
    cT
    cS
    vf
    cE
    @15
    cH
    cK
    cO
    cW
    tendospcan.b
    tendospcan.h
    tendospcan.t
    tendospcan.e
    tendospcan.o
    tendoid0
    syl112anc
    3bitr3d
    biimpd
    impancom
    necon1d
    @13
    @0
    @4
    @5
    @17
    @10
    wb
    @0
    @1
    @6
    @9
    simpl1
    @4
    @5
    @0
    @1
    @9
    simpl3l
    @4
    @5
    @0
    @1
    @9
    simpl3r
    cB
    cT
    cF
    cG
    cH
    cK
    cW
    tendospcan.b
    tendospcan.h
    tendospcan.t
    ltrncoidN
    syl3anc
    sylibd
    3exp1
    com24
    imp5a
    com24
    3imp
    cF
    cG
    cS
    fveq2
    impbid1
end
