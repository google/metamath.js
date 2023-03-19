include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "necomd.mm"
include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wb.mm"
include "xrleltne.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem xrleneltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrleneltd.a: |- ( ph -> A e. RR* )
  assume xrleneltd.b: |- ( ph -> B e. RR* )
  assume xrleneltd.alb: |- ( ph -> A <_ B )
  assume xrleneltd.anb: |- ( ph -> A =/= B )


  assert |- ( ph -> A < B )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    wne
    #
    wph
    cA
    cB
    xrleneltd.anb
    necomd
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
    @0
    @1
    wb
    xrleneltd.a
    xrleneltd.b
    xrleneltd.alb
    cA
    cB
    xrleltne
    syl3anc
    mpbird
end
