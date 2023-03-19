include "cr.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cvol.mm"
include "cdm.mm"
include "snssi.mm"
include "ovolsn.mm"
include "nulmbl.mm"
include "syl2anc.mm"

theorem snmbl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. RR -> { A } e. dom vol )

  proof
    cA
    cr
    wcel
    cA
    csn
    #
    cr
    wss
    @0
    covol
    cfv
    cc0
    wceq
    @0
    cvol
    cdm
    wcel
    cA
    cr
    snssi
    cA
    ovolsn
    @0
    nulmbl
    syl2anc
end
