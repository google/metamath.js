include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wn.mm"
include "xrlenltd.mm"
include "mpbid.mm"
include "intn3an2d.mm"
include "wb.mm"
include "elioc1.mm"
include "syl2anc.mm"
include "mtbird.mm"

theorem lenelioc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume lenelioc.1: |- ( ph -> A e. RR* )
  assume lenelioc.2: |- ( ph -> B e. RR* )
  assume lenelioc.3: |- ( ph -> C e. RR* )
  assume lenelioc.4: |- ( ph -> C <_ A )


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
    cxr
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
    @2
    @1
    @3
    wph
    cC
    cA
    cle
    wbr
    @2
    wn
    lenelioc.4
    wph
    cC
    cA
    lenelioc.3
    lenelioc.1
    xrlenltd
    mpbid
    intn3an2d
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @4
    wb
    lenelioc.1
    lenelioc.2
    cA
    cB
    cC
    elioc1
    syl2anc
    mtbird
end
