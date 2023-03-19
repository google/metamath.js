include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absmul.mm"
include "syl2anc.mm"

theorem absmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( abs ` ( A x. B ) ) = ( ( abs ` A ) x. ( abs ` B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cabs
    cfv
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    cmul
    co
    wceq
    abscld.1
    abssubd.2
    cA
    cB
    absmul
    syl2anc
end
