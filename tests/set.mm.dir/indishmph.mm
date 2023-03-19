include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "c0.mm"
include "cpr.mm"
include "chmph.mm"
include "bren.mm"
include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "ccn.mm"
include "ccnv.mm"
include "cmap.mm"
include "wf.mm"
include "f1of.mm"
include "cvv.mm"
include "wfo.mm"
include "cdm.mm"
include "f1odm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "f1ofo.mm"
include "fornex.mm"
include "sylc.mm"
include "elmapd.mm"
include "mpbird.mm"
include "ctopon.mm"
include "cfv.mm"
include "wceq.mm"
include "indistopon.mm"
include "syl.mm"
include "cnindis.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "f1ocnv.mm"
include "ishmeo.mm"
include "sylanbrc.mm"
include "hmphi.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem indishmph
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( A ~~ B -> { (/) , A } ~= { (/) , B } )

  proof
    cA
    cB
    cen
    wbr
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    c0
    cA
    cpr
    #
    c0
    cB
    cpr
    #
    chmph
    wbr
    #
    cA
    cB
    vf
    bren
    @1
    @4
    vf
    @1
    @0
    @2
    @3
    chmeo
    co
    wcel
    #
    @4
    @1
    @0
    @2
    @3
    ccn
    co
    #
    wcel
    @0
    ccnv
    #
    @3
    @2
    ccn
    co
    #
    wcel
    @5
    @1
    @0
    cB
    cA
    cmap
    co
    #
    @6
    @1
    @0
    @9
    wcel
    cA
    cB
    @0
    wf
    cA
    cB
    @0
    f1of
    @1
    cB
    cA
    @0
    cvv
    cvv
    @1
    cA
    cvv
    wcel
    #
    cA
    cB
    @0
    wfo
    cB
    cvv
    wcel
    #
    @1
    cA
    @0
    cdm
    cvv
    cA
    cB
    @0
    f1odm
    @0
    vf
    vex
    dmex
    syl6eqelr
    #
    cA
    cB
    @0
    f1ofo
    cA
    cB
    cvv
    @0
    fornex
    sylc
    #
    @12
    elmapd
    mpbird
    @1
    @2
    cA
    ctopon
    cfv
    wcel
    #
    @11
    @6
    @9
    wceq
    @1
    @10
    @14
    @12
    cA
    cvv
    indistopon
    syl
    @13
    cB
    @2
    cvv
    cA
    cnindis
    syl2anc
    eleqtrrd
    @1
    @7
    cA
    cB
    cmap
    co
    #
    @8
    @1
    @7
    @15
    wcel
    cB
    cA
    @7
    wf
    #
    @1
    cB
    cA
    @7
    wf1o
    @16
    cA
    cB
    @0
    f1ocnv
    cB
    cA
    @7
    f1of
    syl
    @1
    cA
    cB
    @7
    cvv
    cvv
    @12
    @13
    elmapd
    mpbird
    @1
    @3
    cB
    ctopon
    cfv
    wcel
    #
    @10
    @8
    @15
    wceq
    @1
    @11
    @17
    @13
    cB
    cvv
    indistopon
    syl
    @12
    cA
    @3
    cvv
    cB
    cnindis
    syl2anc
    eleqtrrd
    @0
    @2
    @3
    ishmeo
    sylanbrc
    @0
    @2
    @3
    hmphi
    syl
    exlimiv
    sylbi
end
