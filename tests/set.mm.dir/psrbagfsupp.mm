include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "wf.mm"
include "psrbag.mm"
include "biimpac.mm"
include "simprd.mm"
include "wb.mm"
include "simpr.mm"
include "psrbagf.mm"
include "ancoms.mm"
include "frnnn0fsupp.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem psrbagfsupp
  let cD: class D
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cX: class X
  assume psrbagfsupp.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }

  disjoint I h
  disjoint X h
  assert |- ( ( X e. D /\ I e. V ) -> X finSupp 0 )

  proof
    cX
    cD
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cX
    cc0
    cfsupp
    wbr
    #
    cX
    ccnv
    cn
    cima
    cfn
    wcel
    #
    @2
    cI
    cn0
    cX
    wf
    #
    @4
    @1
    @0
    @5
    @4
    wa
    cD
    vh
    cX
    cI
    cV
    psrbagfsupp.d
    psrbag
    biimpac
    simprd
    @2
    @1
    @5
    @3
    @4
    wb
    @0
    @1
    simpr
    @1
    @0
    @5
    cD
    vh
    cX
    cI
    cV
    psrbagfsupp.d
    psrbagf
    ancoms
    cX
    cI
    cV
    frnnn0fsupp
    syl2anc
    mpbird
end
