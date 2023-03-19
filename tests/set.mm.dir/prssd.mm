include "wcel.mm"
include "cpr.mm"
include "wss.mm"
include "prssi.mm"
include "syl2anc.mm"

theorem prssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume prssd.1: |- ( ph -> A e. C )
  assume prssd.2: |- ( ph -> B e. C )


  assert |- ( ph -> { A , B } C_ C )

  proof
    wph
    cA
    cC
    wcel
    cB
    cC
    wcel
    cA
    cB
    cpr
    cC
    wss
    prssd.1
    prssd.2
    cA
    cB
    cC
    prssi
    syl2anc
end
