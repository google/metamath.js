include "crrv.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "co.mm"
include "cuni.mm"
include "cmap.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "rrvmbfm.mm"
include "cprb.mm"
include "csiga.mm"
include "crn.mm"
include "domprobsiga.mm"
include "syl.mm"
include "brsigarn.mm"
include "elrnsiga.mm"
include "mp1i.mm"
include "ismbfm.mm"
include "unibrsiga.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wb.mm"
include "reex.mm"
include "uniexg.mm"
include "elmapg.mm"
include "sylancr.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "3bitrd.mm"

theorem isrrvv
  let wph: wff ph
  let vy: setvar y
  let cP: class P
  let cX: class X
  let vp: setvar p
  assume isrrvv.1: |- ( ph -> P e. Prob )

  disjoint P y
  disjoint X y
  disjoint p y
  disjoint P p
  assert |- ( ph -> ( X e. ( rRndVar ` P ) <-> ( X : U. dom P --> RR /\ A. y e. BrSiga ( `' X " y ) e. dom P ) ) )

  proof
    wph
    cX
    cP
    crrv
    cfv
    wcel
    cX
    cP
    cdm
    #
    cbrsiga
    cmbfm
    co
    wcel
    cX
    cbrsiga
    cuni
    #
    @0
    cuni
    #
    cmap
    co
    #
    wcel
    #
    cX
    ccnv
    vy
    cv
    cima
    @0
    wcel
    vy
    cbrsiga
    wral
    #
    wa
    @2
    cr
    cX
    wf
    #
    @5
    wa
    wph
    cP
    cX
    isrrvv.1
    rrvmbfm
    wph
    vy
    @0
    cbrsiga
    cX
    wph
    cP
    cprb
    wcel
    @0
    csiga
    crn
    cuni
    #
    wcel
    #
    isrrvv.1
    cP
    domprobsiga
    syl
    #
    cbrsiga
    cr
    csiga
    cfv
    wcel
    cbrsiga
    @7
    wcel
    wph
    brsigarn
    cbrsiga
    cr
    elrnsiga
    mp1i
    ismbfm
    wph
    @4
    @6
    @5
    @4
    cX
    cr
    @2
    cmap
    co
    #
    wcel
    #
    wph
    @6
    @3
    @10
    cX
    @1
    cr
    @2
    cmap
    unibrsiga
    oveq1i
    eleq2i
    wph
    cr
    cvv
    wcel
    @2
    cvv
    wcel
    #
    @11
    @6
    wb
    reex
    wph
    @8
    @12
    @9
    @0
    @7
    uniexg
    syl
    cr
    @2
    cX
    cvv
    cvv
    elmapg
    sylancr
    syl5bb
    anbi1d
    3bitrd
end
