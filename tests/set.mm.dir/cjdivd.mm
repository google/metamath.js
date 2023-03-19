include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjdiv.mm"
include "syl3anc.mm"

theorem cjdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )
  assume cjdivd.2: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( * ` ( A / B ) ) = ( ( * ` A ) / ( * ` B ) ) )

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
    ccj
    cfv
    cA
    ccj
    cfv
    cB
    ccj
    cfv
    cdiv
    co
    wceq
    recld.1
    readdd.2
    cjdivd.2
    cA
    cB
    cjdiv
    syl3anc
end
