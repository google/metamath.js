include "cgic.mm"
include "wbr.mm"
include "cv.mm"
include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "csubg.mm"
include "cfv.mm"
include "cen.mm"
include "c0.mm"
include "wne.mm"
include "brgic.mm"
include "n0.mm"
include "bitri.mm"
include "cima.mm"
include "ccnv.mm"
include "fvexd.mm"
include "cvv.mm"
include "vex.mm"
include "imaex.mm"
include "2a1i.mm"
include "cnvex.mm"
include "wceq.mm"
include "wa.mm"
include "cghm.mm"
include "gimghm.mm"
include "ghmima.mm"
include "sylan.mm"
include "cbs.mm"
include "wf1.mm"
include "wss.mm"
include "wf1o.mm"
include "eqid.mm"
include "gimf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "subgss.mm"
include "f1imacnv.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "jca.mm"
include "eleq1.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "impr.mm"
include "ghmpreima.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foimacnv.mm"
include "impbida.mm"
include "en2d.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem gicsubgen
  let cR: class R
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( R ~=g S -> ( SubGrp ` R ) ~~ ( SubGrp ` S ) )

  proof
    cR
    cS
    cgic
    wbr
    #
    va
    cv
    #
    cR
    cS
    cgim
    co
    #
    wcel
    #
    va
    wex
    #
    cR
    csubg
    cfv
    #
    cS
    csubg
    cfv
    #
    cen
    wbr
    #
    @0
    @2
    c0
    wne
    @4
    cR
    cS
    brgic
    va
    @2
    n0
    bitri
    @3
    @7
    va
    @3
    vb
    vc
    @5
    @6
    @1
    vb
    cv
    #
    cima
    #
    @1
    ccnv
    #
    vc
    cv
    #
    cima
    #
    @3
    cR
    csubg
    fvexd
    @3
    cS
    csubg
    fvexd
    @9
    cvv
    wcel
    @3
    @8
    @5
    wcel
    #
    @1
    @8
    va
    vex
    #
    imaex
    2a1i
    @12
    cvv
    wcel
    @3
    @11
    @6
    wcel
    #
    @10
    @11
    @1
    @14
    cnvex
    imaex
    2a1i
    @3
    @13
    @11
    @9
    wceq
    #
    wa
    #
    @15
    @8
    @12
    wceq
    #
    wa
    #
    @3
    @13
    @16
    @19
    @3
    @13
    wa
    #
    @19
    @16
    @9
    @6
    wcel
    #
    @8
    @10
    @9
    cima
    #
    wceq
    #
    wa
    @20
    @21
    @23
    @3
    @1
    cR
    cS
    cghm
    co
    wcel
    #
    @13
    @21
    cR
    cS
    @1
    gimghm
    #
    cR
    cS
    @8
    @1
    ghmima
    sylan
    @20
    @22
    @8
    @3
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    @1
    wf1
    #
    @8
    @26
    wss
    @22
    @8
    wceq
    @13
    @3
    @26
    @27
    @1
    wf1o
    #
    @28
    @26
    @27
    cR
    cS
    @1
    @26
    eqid
    #
    @27
    eqid
    #
    gimf1o
    #
    @26
    @27
    @1
    f1of1
    syl
    @26
    @8
    cR
    @30
    subgss
    @26
    @27
    @8
    @1
    f1imacnv
    syl2an
    eqcomd
    jca
    @16
    @15
    @21
    @18
    @23
    @11
    @9
    @6
    eleq1
    @16
    @12
    @22
    @8
    @11
    @9
    @10
    imaeq2
    eqeq2d
    anbi12d
    syl5ibrcom
    impr
    @3
    @15
    @18
    @17
    @3
    @15
    wa
    #
    @17
    @18
    @12
    @5
    wcel
    #
    @11
    @1
    @12
    cima
    #
    wceq
    #
    wa
    @33
    @34
    @36
    @3
    @24
    @15
    @34
    @25
    cR
    cS
    @1
    @11
    ghmpreima
    sylan
    @33
    @35
    @11
    @3
    @26
    @27
    @1
    wfo
    #
    @11
    @27
    wss
    @35
    @11
    wceq
    @15
    @3
    @29
    @37
    @32
    @26
    @27
    @1
    f1ofo
    syl
    @27
    @11
    cS
    @31
    subgss
    @26
    @27
    @11
    @1
    foimacnv
    syl2an
    eqcomd
    jca
    @18
    @13
    @34
    @16
    @36
    @8
    @12
    @5
    eleq1
    @18
    @9
    @35
    @11
    @8
    @12
    @1
    imaeq2
    eqeq2d
    anbi12d
    syl5ibrcom
    impr
    impbida
    en2d
    exlimiv
    sylbi
end
