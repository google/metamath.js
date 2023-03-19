include "wf.mm"
include "wf1o.mm"
include "wa.mm"
include "ccom.mm"
include "ccnv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cima.mm"
include "cv.mm"
include "wss.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "dmcoss.mm"
include "sstri.mm"
include "wceq.mm"
include "f1ocnv.mm"
include "adantl.mm"
include "f1odm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "crn.mm"
include "imassrn.mm"
include "f1of.mm"
include "frn.mm"
include "syl5ss.mm"
include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "wfn.mm"
include "wb.mm"
include "simpl.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffn.mm"
include "fnelnfp.mm"
include "sylan.mm"
include "f1ofn.mm"
include "fvco2.mm"
include "ad2antrr.mm"
include "ffvelrn.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "simplr.mm"
include "simpll.mm"
include "simpr.mm"
include "f1ocnvfvb.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "necon3bid.mm"
include "necom.mm"
include "wf1.mm"
include "f1of1.mm"
include "ad2antlr.mm"
include "fdm.mm"
include "f1elima.mm"
include "f1ocnvfv2.mm"
include "adantll.mm"
include "eleq1d.mm"
include "3bitr3rd.mm"
include "syl5bb.mm"
include "3bitrd.mm"
include "eqrdav.mm"

theorem f1omvdconj
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A --> A /\ G : A -1-1-onto-> A ) -> dom ( ( ( G o. F ) o. `' G ) \ _I ) = ( G " dom ( F \ _I ) ) )

  proof
    cA
    cA
    cF
    wf
    #
    cA
    cA
    cG
    wf1o
    #
    wa
    #
    vx
    cG
    cF
    ccom
    #
    cG
    ccnv
    #
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cG
    cF
    cid
    cdif
    #
    cdm
    #
    cima
    #
    cA
    @2
    @7
    cA
    vx
    cv
    #
    @2
    @4
    cdm
    #
    @7
    cA
    @7
    @5
    cdm
    #
    @12
    @6
    @5
    wss
    @7
    @13
    wss
    @5
    cid
    difss
    @6
    @5
    dmss
    ax-mp
    @3
    @4
    dmcoss
    sstri
    @2
    cA
    cA
    @4
    wf1o
    #
    @12
    cA
    wceq
    @1
    @14
    @0
    cA
    cA
    cG
    f1ocnv
    adantl
    #
    cA
    cA
    @4
    f1odm
    syl
    syl5sseq
    sselda
    @2
    @10
    cA
    @11
    @2
    @10
    cG
    crn
    #
    cA
    cG
    @9
    imassrn
    @2
    cA
    cA
    cG
    wf
    #
    @16
    cA
    wss
    @1
    @17
    @0
    cA
    cA
    cG
    f1of
    adantl
    #
    cA
    cA
    cG
    frn
    syl
    syl5ss
    sselda
    @2
    @11
    cA
    wcel
    #
    wa
    #
    @11
    @7
    wcel
    #
    @11
    @5
    cfv
    #
    @11
    wne
    #
    @11
    @4
    cfv
    #
    @24
    cF
    cfv
    #
    wne
    #
    @11
    @10
    wcel
    #
    @2
    @5
    cA
    wfn
    #
    @19
    @21
    @23
    wb
    @2
    cA
    cA
    @5
    wf
    #
    @28
    @2
    cA
    cA
    @3
    wf
    #
    cA
    cA
    @4
    wf
    #
    @29
    @2
    @17
    @0
    @30
    @18
    @0
    @1
    simpl
    cA
    cA
    cA
    cG
    cF
    fco
    syl2anc
    @2
    @14
    @31
    @15
    cA
    cA
    @4
    f1of
    syl
    #
    cA
    cA
    cA
    @3
    @4
    fco
    syl2anc
    cA
    cA
    @5
    ffn
    syl
    cA
    @5
    @11
    fnelnfp
    sylan
    @20
    @22
    @11
    @24
    @25
    @20
    @22
    @11
    wceq
    @25
    cG
    cfv
    #
    @11
    wceq
    #
    @24
    @25
    wceq
    #
    @20
    @22
    @33
    @11
    @20
    @22
    @24
    @3
    cfv
    #
    @33
    @2
    @4
    cA
    wfn
    #
    @19
    @22
    @36
    wceq
    @2
    @14
    @37
    @15
    cA
    cA
    @4
    f1ofn
    syl
    cA
    @3
    @4
    @11
    fvco2
    sylan
    @20
    cF
    cA
    wfn
    #
    @24
    cA
    wcel
    #
    @36
    @33
    wceq
    @0
    @38
    @1
    @19
    cA
    cA
    cF
    ffn
    ad2antrr
    #
    @2
    @31
    @19
    @39
    @32
    cA
    cA
    @11
    @4
    ffvelrn
    sylan
    #
    cA
    cG
    cF
    @24
    fvco2
    syl2anc
    eqtrd
    eqeq1d
    @20
    @1
    @25
    cA
    wcel
    #
    @19
    @34
    @35
    wb
    @0
    @1
    @19
    simplr
    @20
    @0
    @39
    @42
    @0
    @1
    @19
    simpll
    @41
    cA
    cA
    @24
    cF
    ffvelrn
    syl2anc
    @2
    @19
    simpr
    cA
    cA
    @25
    @11
    cG
    f1ocnvfvb
    syl3anc
    bitrd
    necon3bid
    @26
    @25
    @24
    wne
    #
    @20
    @27
    @24
    @25
    necom
    @20
    @24
    cG
    cfv
    #
    @10
    wcel
    #
    @24
    @9
    wcel
    #
    @27
    @43
    @20
    cA
    cA
    cG
    wf1
    #
    @39
    @9
    cA
    wss
    #
    @45
    @46
    wb
    @1
    @47
    @0
    @19
    cA
    cA
    cG
    f1of1
    ad2antlr
    @41
    @0
    @48
    @1
    @19
    @0
    cF
    cdm
    #
    @9
    cA
    @8
    cF
    wss
    @9
    @49
    wss
    cF
    cid
    difss
    @8
    cF
    dmss
    ax-mp
    cA
    cA
    cF
    fdm
    syl5sseq
    ad2antrr
    cA
    cA
    cG
    @24
    @9
    f1elima
    syl3anc
    @20
    @44
    @11
    @10
    @1
    @19
    @44
    @11
    wceq
    @0
    cA
    cA
    @11
    cG
    f1ocnvfv2
    adantll
    eleq1d
    @20
    @38
    @39
    @46
    @43
    wb
    @40
    @41
    cA
    cF
    @24
    fnelnfp
    syl2anc
    3bitr3rd
    syl5bb
    3bitrd
    eqrdav
end
