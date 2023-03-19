include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absdiv.mm"
include "syl3anc.mm"

theorem absdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )
  assume absdivd.2: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( abs ` ( A / B ) ) = ( ( abs ` A ) / ( abs ` B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cabs
    cfv
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    cdiv
    co
    wceq
    abscld.1
    abssubd.2
    absdivd.2
    cA
    cB
    absdiv
    syl3anc
end
