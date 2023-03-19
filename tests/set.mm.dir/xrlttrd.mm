include "clt.mm"
include "wbr.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "xrlttr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem xrlttrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrlttrd.1: |- ( ph -> A e. RR* )
  assume xrlttrd.2: |- ( ph -> B e. RR* )
  assume xrlttrd.3: |- ( ph -> C e. RR* )
  assume xrlttrd.4: |- ( ph -> A < B )
  assume xrlttrd.5: |- ( ph -> B < C )


  assert |- ( ph -> A < C )

  proof
    wph
    cA
    cB
    clt
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
    xrlttrd.4
    xrlttrd.5
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
    xrlttr
    syl3anc
    mp2and
end
