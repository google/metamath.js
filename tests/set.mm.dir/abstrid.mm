include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "abstri.mm"
include "syl2anc.mm"

theorem abstrid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( abs ` ( A + B ) ) <_ ( ( abs ` A ) + ( abs ` B ) ) )

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
    caddc
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
    abstri
    syl2anc
end
