include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "wfn.mm"
include "ccatfval.mm"
include "fvex.mm"
include "ifex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "syl.mm"

theorem ccatvalfn
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( A ++ B ) Fn ( 0 ..^ ( ( # ` A ) + ( # ` B ) ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    cB
    @0
    wcel
    wa
    cA
    cB
    cconcat
    co
    #
    vx
    cc0
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    caddc
    co
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @2
    cfzo
    co
    wcel
    #
    @4
    cA
    cfv
    #
    @4
    @2
    cmin
    co
    #
    cB
    cfv
    #
    cif
    #
    cmpt
    #
    wceq
    #
    @1
    @3
    wfn
    #
    vx
    cA
    cB
    @0
    @0
    ccatfval
    @11
    @12
    @10
    @3
    wfn
    vx
    @3
    @9
    @10
    @5
    @6
    @8
    @4
    cA
    fvex
    @7
    cB
    fvex
    ifex
    @10
    eqid
    fnmpti
    @3
    @1
    @10
    fneq1
    mpbiri
    syl
end
