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
include "rexrd.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "intnand.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mtbird.mm"

theorem gtnelicc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume gtnelicc.a: |- ( ph -> A e. RR* )
  assume gtnelicc.b: |- ( ph -> B e. RR )
  assume gtnelicc.c: |- ( ph -> C e. RR* )
  assume gtnelicc.bltc: |- ( ph -> B < C )


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
    gtnelicc.bltc
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
    wph
    cB
    gtnelicc.b
    rexrd
    #
    gtnelicc.c
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
    gtnelicc.a
    @8
    gtnelicc.c
    cA
    cB
    cC
    elicc4
    syl3anc
    mtbird
end
