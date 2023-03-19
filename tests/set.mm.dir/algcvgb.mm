include "wcel.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "ffvelrni.mm"
include "syl.mm"
include "algcvgblem.mm"
include "syl2anc.mm"

theorem algcvgb
  let cC: class C
  let cS: class S
  let cF: class F
  let cX: class X
  assume algcvgb.1: |- F : S --> S
  assume algcvgb.2: |- C : S --> NN0


  assert |- ( X e. S -> ( ( ( C ` ( F ` X ) ) =/= 0 -> ( C ` ( F ` X ) ) < ( C ` X ) ) <-> ( ( ( C ` X ) =/= 0 -> ( C ` ( F ` X ) ) < ( C ` X ) ) /\ ( ( C ` X ) = 0 -> ( C ` ( F ` X ) ) = 0 ) ) ) )

  proof
    cX
    cS
    wcel
    #
    cX
    cC
    cfv
    #
    cn0
    wcel
    cX
    cF
    cfv
    #
    cC
    cfv
    #
    cn0
    wcel
    #
    @3
    cc0
    wne
    @3
    @1
    clt
    wbr
    #
    wi
    @1
    cc0
    wne
    @5
    wi
    @1
    cc0
    wceq
    @3
    cc0
    wceq
    wi
    wa
    wb
    cS
    cn0
    cX
    cC
    algcvgb.2
    ffvelrni
    @0
    @2
    cS
    wcel
    @4
    cS
    cS
    cX
    cF
    algcvgb.1
    ffvelrni
    cS
    cn0
    @2
    cC
    algcvgb.2
    ffvelrni
    syl
    @1
    @3
    algcvgblem
    syl2anc
end
