include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "xrlelttr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem xrlelttrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrlttrd.1: |- ( ph -> A e. RR* )
  assume xrlttrd.2: |- ( ph -> B e. RR* )
  assume xrlttrd.3: |- ( ph -> C e. RR* )
  assume xrlelttrd.4: |- ( ph -> A <_ B )
  assume xrlelttrd.5: |- ( ph -> B < C )


  assert |- ( ph -> A < C )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    xrlelttrd.4
    xrlelttrd.5
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    @0
    @1
    wa
    @2
    wi
    xrlttrd.1
    xrlttrd.2
    xrlttrd.3
    cA
    cB
    cC
    xrlelttr
    syl3anc
    mp2and
end
