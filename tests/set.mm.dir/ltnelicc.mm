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
include "intnanrd.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mtbird.mm"

theorem ltnelicc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltnelicc.a: |- ( ph -> A e. RR )
  assume ltnelicc.b: |- ( ph -> B e. RR* )
  assume ltnelicc.c: |- ( ph -> C e. RR* )
  assume ltnelicc.clta: |- ( ph -> C < A )


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
    @1
    @2
    wph
    cC
    cA
    clt
    wbr
    #
    @1
    wn
    #
    ltnelicc.clta
    wph
    cC
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    @4
    @5
    wb
    ltnelicc.c
    wph
    cA
    ltnelicc.a
    rexrd
    #
    cC
    cA
    xrltnle
    syl2anc
    mpbid
    intnanrd
    wph
    @7
    cB
    cxr
    wcel
    @6
    @0
    @3
    wb
    @8
    ltnelicc.b
    ltnelicc.c
    cA
    cB
    cC
    elicc4
    syl3anc
    mtbird
end
