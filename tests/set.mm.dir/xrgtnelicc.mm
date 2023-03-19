include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "wn.mm"
include "cxr.mm"
include "wb.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "intnand.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mtbird.mm"

theorem xrgtnelicc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrgtnelicc.1: |- ( ph -> A e. RR* )
  assume xrgtnelicc.2: |- ( ph -> B e. RR* )
  assume xrgtnelicc.3: |- ( ph -> C e. RR* )
  assume xrgtnelicc.4: |- ( ph -> B < C )


  assert |- ( ph -> -. C e. ( A [,] B ) )

  proof
    wph
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    wa
    #
    wph
    @2
    @1
    wph
    cB
    cC
    clt
    wbr
    #
    @2
    wn
    #
    xrgtnelicc.4
    wph
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    @4
    @5
    wb
    xrgtnelicc.2
    xrgtnelicc.3
    cB
    cC
    xrltnle
    syl2anc
    mpbid
    intnand
    wph
    cA
    cxr
    wcel
    @6
    @7
    @0
    @3
    wb
    xrgtnelicc.1
    xrgtnelicc.2
    xrgtnelicc.3
    cA
    cB
    cC
    elicc4
    syl3anc
    mtbird
end
