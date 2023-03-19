include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "xrltne.mm"
include "syl3anc.mm"

theorem xrgtned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrgtned.1: |- ( ph -> A e. RR* )
  assume xrgtned.2: |- ( ph -> B e. RR* )
  assume xrgtned.3: |- ( ph -> A < B )


  assert |- ( ph -> B =/= A )

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
    clt
    wbr
    cB
    cA
    wne
    xrgtned.1
    xrgtned.2
    xrgtned.3
    cA
    cB
    xrltne
    syl3anc
end
