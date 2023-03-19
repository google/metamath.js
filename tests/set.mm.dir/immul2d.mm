include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "immul2.mm"
include "syl2anc.mm"

theorem immul2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume crred.1: |- ( ph -> A e. RR )
  assume remul2d.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Im ` ( A x. B ) ) = ( A x. ( Im ` B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cim
    cfv
    cA
    cB
    cim
    cfv
    cmul
    co
    wceq
    crred.1
    remul2d.2
    cA
    cB
    immul2
    syl2anc
end
