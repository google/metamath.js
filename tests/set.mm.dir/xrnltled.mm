include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem xrnltled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrnltled.1: |- ( ph -> A e. RR* )
  assume xrnltled.2: |- ( ph -> B e. RR* )
  assume xrnltled.3: |- ( ph -> -. B < A )


  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    clt
    wbr
    wn
    #
    xrnltled.3
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @1
    wb
    xrnltled.1
    xrnltled.2
    cA
    cB
    xrlenlt
    syl2anc
    mpbird
end
