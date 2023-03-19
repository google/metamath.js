include "cpw.mm"
include "cv.mm"
include "cima.mm"
include "ccnv.mm"
include "cmpt.mm"
include "eqid.mm"
include "wcel.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "wfo.mm"
include "wceq.mm"
include "wf1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "forn.mm"
include "syl5sseq.mm"
include "cvv.mm"
include "wb.mm"
include "elpwg.mm"
include "mpbird.mm"
include "adantr.mm"
include "cdm.mm"
include "dfdm4.mm"
include "f1odm.mm"
include "syl5eqr.mm"
include "wa.mm"
include "elpwi.mm"
include "adantl.mm"
include "foimacnv.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1imacnv.mm"
include "impbid.mm"
include "f1o2d.mm"

theorem f1opw2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  assume f1opw2.1: |- ( ph -> F : A -1-1-onto-> B )
  assume f1opw2.2: |- ( ph -> ( `' F " a ) e. _V )
  assume f1opw2.3: |- ( ph -> ( F " b ) e. _V )

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B )

  proof
    wph
    vb
    va
    cA
    cpw
    #
    cB
    cpw
    #
    cF
    vb
    cv
    #
    cima
    #
    cF
    ccnv
    #
    va
    cv
    #
    cima
    #
    vb
    @0
    @3
    cmpt
    #
    @7
    eqid
    wph
    @3
    @1
    wcel
    #
    @2
    @0
    wcel
    #
    wph
    @8
    @3
    cB
    wss
    #
    wph
    cF
    crn
    #
    @3
    cB
    cF
    @2
    imassrn
    wph
    cA
    cB
    cF
    wfo
    #
    @11
    cB
    wceq
    wph
    cA
    cB
    cF
    wf1o
    #
    @12
    f1opw2.1
    cA
    cB
    cF
    f1ofo
    syl
    #
    cA
    cB
    cF
    forn
    syl
    syl5sseq
    wph
    @3
    cvv
    wcel
    @8
    @10
    wb
    f1opw2.3
    @3
    cB
    cvv
    elpwg
    syl
    mpbird
    adantr
    wph
    @6
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wph
    @15
    @6
    cA
    wss
    #
    wph
    @4
    crn
    #
    @6
    cA
    @4
    @5
    imassrn
    wph
    @18
    cF
    cdm
    #
    cA
    cF
    dfdm4
    wph
    @13
    @19
    cA
    wceq
    f1opw2.1
    cA
    cB
    cF
    f1odm
    syl
    syl5eqr
    syl5sseq
    wph
    @6
    cvv
    wcel
    @15
    @17
    wb
    f1opw2.2
    @6
    cA
    cvv
    elpwg
    syl
    mpbird
    adantr
    wph
    @9
    @16
    wa
    #
    wa
    #
    @2
    @6
    wceq
    #
    @5
    @3
    wceq
    #
    @21
    @23
    @22
    @5
    cF
    @6
    cima
    #
    wceq
    @21
    @24
    @5
    wph
    @12
    @5
    cB
    wss
    #
    @24
    @5
    wceq
    @20
    @14
    @16
    @25
    @9
    @5
    cB
    elpwi
    adantl
    cA
    cB
    @5
    cF
    foimacnv
    syl2an
    eqcomd
    @22
    @3
    @24
    @5
    @2
    @6
    cF
    imaeq2
    eqeq2d
    syl5ibrcom
    @21
    @22
    @23
    @2
    @4
    @3
    cima
    #
    wceq
    @21
    @26
    @2
    wph
    cA
    cB
    cF
    wf1
    #
    @2
    cA
    wss
    #
    @26
    @2
    wceq
    @20
    wph
    @13
    @27
    f1opw2.1
    cA
    cB
    cF
    f1of1
    syl
    @9
    @28
    @16
    @2
    cA
    elpwi
    adantr
    cA
    cB
    @2
    cF
    f1imacnv
    syl2an
    eqcomd
    @23
    @6
    @26
    @2
    @5
    @3
    @4
    imaeq2
    eqeq2d
    syl5ibrcom
    impbid
    f1o2d
end
