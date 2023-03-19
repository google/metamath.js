include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wb.mm"
include "xrlenlt.mm"
include "syl2anc.mm"

theorem xrlenltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrlenltd.a: |- ( ph -> A e. RR* )
  assume xrlenltd.b: |- ( ph -> B e. RR* )


  assert |- ( ph -> ( A <_ B <-> -. B < A ) )

  proof
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    cB
    cA
    clt
    wbr
    wn
    wb
    xrlenltd.a
    xrlenltd.b
    cA
    cB
    xrlenlt
    syl2anc
end
