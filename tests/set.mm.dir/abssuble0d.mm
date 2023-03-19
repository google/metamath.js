include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "abssuble0.mm"
include "syl3anc.mm"

theorem abssuble0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume absltd.1: |- ( ph -> A e. RR )
  assume absltd.2: |- ( ph -> B e. RR )
  assume abssubge0d.2: |- ( ph -> A <_ B )


  assert |- ( ph -> ( abs ` ( A - B ) ) = ( B - A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
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
    wceq
    absltd.1
    absltd.2
    abssubge0d.2
    cA
    cB
    abssuble0
    syl3anc
end
