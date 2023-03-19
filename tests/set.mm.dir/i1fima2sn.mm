include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "citg1.mm"
include "cdm.mm"
include "wn.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "cr.mm"
include "eldifn.mm"
include "elsni.mm"
include "snidg.mm"
include "eqeltrrd.mm"
include "nsyl.mm"
include "i1fima2.mm"
include "sylan2.mm"

theorem i1fima2sn
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. dom S.1 /\ A e. ( B \ { 0 } ) ) -> ( vol ` ( `' F " { A } ) ) e. RR )

  proof
    cA
    cB
    cc0
    csn
    #
    cdif
    wcel
    #
    cF
    citg1
    cdm
    wcel
    cc0
    cA
    csn
    #
    wcel
    #
    wn
    cF
    ccnv
    @2
    cima
    cvol
    cfv
    cr
    wcel
    @1
    cA
    @0
    wcel
    @3
    cA
    cB
    @0
    eldifn
    @3
    cc0
    cA
    @0
    cc0
    cA
    elsni
    cc0
    @2
    snidg
    eqeltrrd
    nsyl
    @2
    cF
    i1fima2
    sylan2
end
