include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "abssub.mm"
include "syl2anc.mm"

theorem abssubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( abs ` ( A - B ) ) = ( abs ` ( B - A ) ) )

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
    cmin
    co
    cabs
    cfv
    cB
    cA
    cmin
    co
    cabs
    cfv
    wceq
    abscld.1
    abssubd.2
    cA
    cB
    abssub
    syl2anc
end
