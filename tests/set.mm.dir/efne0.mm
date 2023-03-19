include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "ce.mm"
include "cfv.mm"
include "ax-1ne0.mm"
include "wceq.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "oveq1.mm"
include "efcan.mm"
include "negcl.mm"
include "efcl.mm"
include "syl.mm"
include "mul02d.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "necon3d.mm"
include "mpi.mm"

theorem efne0
  let cA: class A


  assert |- ( A e. CC -> ( exp ` A ) =/= 0 )

  proof
    cA
    cc
    wcel
    #
    c1
    cc0
    wne
    cA
    ce
    cfv
    #
    cc0
    wne
    ax-1ne0
    @0
    @1
    cc0
    c1
    cc0
    @1
    cc0
    wceq
    @1
    cA
    cneg
    #
    ce
    cfv
    #
    cmul
    co
    #
    cc0
    @3
    cmul
    co
    #
    wceq
    @0
    c1
    cc0
    wceq
    @1
    cc0
    @3
    cmul
    oveq1
    @0
    @4
    c1
    @5
    cc0
    cA
    efcan
    @0
    @3
    @0
    @2
    cc
    wcel
    @3
    cc
    wcel
    cA
    negcl
    @2
    efcl
    syl
    mul02d
    eqeq12d
    syl5ib
    necon3d
    mpi
end
