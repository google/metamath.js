include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "abs2dif2.mm"
include "syl2anc.mm"

theorem abs2dif2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( abs ` ( A - B ) ) <_ ( ( abs ` A ) + ( abs ` B ) ) )

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
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    caddc
    co
    cle
    wbr
    abscld.1
    abssubd.2
    cA
    cB
    abs2dif2
    syl2anc
end
