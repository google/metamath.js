include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "xrletr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem xrletrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrlttrd.1: |- ( ph -> A e. RR* )
  assume xrlttrd.2: |- ( ph -> B e. RR* )
  assume xrlttrd.3: |- ( ph -> C e. RR* )
  assume xrletrd.4: |- ( ph -> A <_ B )
  assume xrletrd.5: |- ( ph -> B <_ C )


  assert |- ( ph -> A <_ C )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    cA
    cC
    cle
    wbr
    #
    xrletrd.4
    xrletrd.5
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
    xrletr
    syl3anc
    mp2and
end
