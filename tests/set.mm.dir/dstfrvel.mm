include "ccnv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "crab.mm"
include "cima.mm"
include "corvc.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "rrvvf.mm"
include "ffvelrnd.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wfun.mm"
include "wb.mm"
include "wf.mm"
include "ffun.mm"
include "syl.mm"
include "rrvdm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "orrvcval4.mm"

theorem dstfrvel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cX: class X
  let vx: setvar x
  assume dstfrv.1: |- ( ph -> P e. Prob )
  assume dstfrv.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orvclteel.1: |- ( ph -> A e. RR )
  assume dstfrvel.1: |- ( ph -> B e. U. dom P )
  assume dstfrvel.2: |- ( ph -> ( X ` B ) <_ A )


  assert |- ( ph -> B e. ( X oRVC <_ A ) )

  proof
    wph
    cB
    cX
    ccnv
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vx
    cr
    crab
    #
    cima
    #
    cX
    cA
    cle
    corvc
    co
    wph
    cB
    cX
    cfv
    #
    @2
    wcel
    #
    cB
    @3
    wcel
    #
    wph
    @4
    cr
    wcel
    @4
    cA
    cle
    wbr
    #
    @5
    wph
    cP
    cdm
    cuni
    #
    cr
    cB
    cX
    wph
    cP
    cX
    dstfrv.1
    dstfrv.2
    rrvvf
    #
    dstfrvel.1
    ffvelrnd
    dstfrvel.2
    @1
    @7
    vx
    @4
    cr
    @0
    @4
    cA
    cle
    breq1
    elrab
    sylanbrc
    wph
    cX
    wfun
    #
    cB
    cX
    cdm
    #
    wcel
    @5
    @6
    wb
    wph
    @8
    cr
    cX
    wf
    @10
    @9
    @8
    cr
    cX
    ffun
    syl
    wph
    cB
    @8
    @11
    dstfrvel.1
    wph
    cP
    cX
    dstfrv.1
    dstfrv.2
    rrvdm
    eleqtrrd
    cB
    @2
    cX
    fvimacnv
    syl2anc
    mpbid
    wph
    vx
    cA
    cP
    cle
    cr
    cX
    dstfrv.1
    dstfrv.2
    orvclteel.1
    orrvcval4
    eleqtrrd
end
