include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "wi.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem xrltled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrltled.a: |- ( ph -> A e. RR* )
  assume xrltled.b: |- ( ph -> B e. RR* )
  assume xrltled.altb: |- ( ph -> A < B )


  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    xrltled.altb
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @1
    wi
    xrltled.a
    xrltled.b
    cA
    cB
    xrltle
    syl2anc
    mpd
end
