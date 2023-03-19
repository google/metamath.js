include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wn.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "intn3an3d.mm"
include "elioc2.mm"
include "mtbird.mm"

theorem gtnelioc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume gtnelioc.a: |- ( ph -> A e. RR* )
  assume gtnelioc.b: |- ( ph -> B e. RR )
  assume gtnelioc.c: |- ( ph -> C e. RR* )
  assume gtnelioc.bltc: |- ( ph -> B < C )


  assert |- ( ph -> -. C e. ( A (,] B ) )

  proof
    wph
    cC
    cA
    cB
    cioc
    co
    wcel
    #
    cC
    cr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    w3a
    #
    wph
    @3
    @1
    @2
    wph
    cB
    cC
    clt
    wbr
    #
    @3
    wn
    #
    gtnelioc.bltc
    wph
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    @5
    @6
    wb
    wph
    cB
    gtnelioc.b
    rexrd
    gtnelioc.c
    cB
    cC
    xrltnle
    syl2anc
    mpbid
    intn3an3d
    wph
    cA
    cxr
    wcel
    cB
    cr
    wcel
    @0
    @4
    wb
    gtnelioc.a
    gtnelioc.b
    cA
    cB
    cC
    elioc2
    syl2anc
    mtbird
end
