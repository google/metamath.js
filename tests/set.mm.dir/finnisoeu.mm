include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccrd.mm"
include "cfv.mm"
include "cep.mm"
include "cv.mm"
include "wiso.mm"
include "wex.mm"
include "wmo.mm"
include "weu.mm"
include "coi.mm"
include "cvv.mm"
include "eqid.mm"
include "oiexg.mm"
include "adantl.mm"
include "cdm.mm"
include "wwe.mm"
include "simpr.mm"
include "wofi.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wb.mm"
include "cen.mm"
include "wbr.mm"
include "oien.mm"
include "ficardid.mm"
include "ensymd.mm"
include "entr.mm"
include "con0.mm"
include "com.mm"
include "oion.mm"
include "ficardom.mm"
include "onomeneq.mm"
include "mpbid.mm"
include "isoeq4.mm"
include "syl.mm"
include "isoeq1.mm"
include "spcegv.mm"
include "sylc.mm"
include "wemoiso2.mm"
include "eu5.mm"
include "sylanbrc.mm"

theorem finnisoeu
  let cA: class A
  let cR: class R
  let vf: setvar f

  disjoint R f
  disjoint A f
  assert |- ( ( R Or A /\ A e. Fin ) -> E! f f Isom _E , R ( ( card ` A ) , A ) )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cA
    ccrd
    cfv
    #
    cA
    cep
    cR
    vf
    cv
    #
    wiso
    #
    vf
    wex
    #
    @5
    vf
    wmo
    #
    @5
    vf
    weu
    @2
    cA
    cR
    coi
    #
    cvv
    wcel
    #
    @3
    cA
    cep
    cR
    @8
    wiso
    #
    @6
    @1
    @9
    @0
    cA
    cR
    @8
    cfn
    @8
    eqid
    #
    oiexg
    adantl
    @2
    @8
    cdm
    #
    cA
    cep
    cR
    @8
    wiso
    #
    @10
    @2
    @1
    cA
    cR
    wwe
    #
    @13
    @0
    @1
    simpr
    #
    cA
    cR
    wofi
    #
    cA
    cR
    @8
    cfn
    @11
    oiiso
    syl2anc
    @2
    @12
    @3
    wceq
    #
    @13
    @10
    wb
    @2
    @12
    @3
    cen
    wbr
    #
    @17
    @2
    @12
    cA
    cen
    wbr
    #
    cA
    @3
    cen
    wbr
    @18
    @2
    @1
    @14
    @19
    @15
    @16
    cA
    cR
    @8
    cfn
    @11
    oien
    syl2anc
    @2
    @3
    cA
    @1
    @3
    cA
    cen
    wbr
    @0
    cA
    ficardid
    adantl
    ensymd
    @12
    cA
    @3
    entr
    syl2anc
    @2
    @12
    con0
    wcel
    #
    @3
    com
    wcel
    #
    @18
    @17
    wb
    @1
    @20
    @0
    cA
    cR
    @8
    cfn
    @11
    oion
    adantl
    @1
    @21
    @0
    cA
    ficardom
    adantl
    @12
    @3
    onomeneq
    syl2anc
    mpbid
    @12
    cA
    @3
    cep
    cR
    @8
    isoeq4
    syl
    mpbid
    @5
    @10
    vf
    @8
    cvv
    @3
    cA
    cep
    cR
    @8
    @4
    isoeq1
    spcegv
    sylc
    @2
    @14
    @7
    @16
    @3
    cA
    cep
    cR
    vf
    wemoiso2
    syl
    @5
    vf
    eu5
    sylanbrc
end
