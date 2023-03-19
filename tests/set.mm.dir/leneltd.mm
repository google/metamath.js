include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "leltned.mm"
include "mpbird.mm"

theorem leneltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume leltned.3: |- ( ph -> A <_ B )
  assume leneltd.4: |- ( ph -> B =/= A )


  assert |- ( ph -> A < B )

  proof
    wph
    cA
    cB
    clt
    wbr
    cB
    cA
    wne
    leneltd.4
    wph
    cA
    cB
    ltd.1
    ltd.2
    leltned.3
    leltned
    mpbird
end
