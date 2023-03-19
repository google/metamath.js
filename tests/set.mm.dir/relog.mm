include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cre.mm"
include "ce.mm"
include "cabs.mm"
include "cr.mm"
include "wceq.mm"
include "logcl.mm"
include "recld.mm"
include "relogef.mm"
include "syl.mm"
include "absef.mm"
include "eflog.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem relog
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( Re ` ( log ` A ) ) = ( log ` ( abs ` A ) ) )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    #
    cA
    clog
    cfv
    #
    cre
    cfv
    #
    ce
    cfv
    #
    clog
    cfv
    #
    @2
    cA
    cabs
    cfv
    #
    clog
    cfv
    @0
    @2
    cr
    wcel
    @4
    @2
    wceq
    @0
    @1
    cA
    logcl
    #
    recld
    @2
    relogef
    syl
    @0
    @3
    @5
    clog
    @0
    @1
    ce
    cfv
    #
    cabs
    cfv
    #
    @3
    @5
    @0
    @1
    cc
    wcel
    @8
    @3
    wceq
    @6
    @1
    absef
    syl
    @0
    @7
    cA
    cabs
    cA
    eflog
    fveq2d
    eqtr3d
    fveq2d
    eqtr3d
end
