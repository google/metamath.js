include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cbr.mm"
include "cfv.mm"
include "chft.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "wf.mm"
include "wceq.mm"
include "bracl.mm"
include "adantr.mm"
include "brafn.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "hfmval.mm"
include "syl3anc.mm"
include "eqcomd.mm"

theorem kbass3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( ( bra ` A ) ` B ) x. ( ( bra ` C ) ` D ) ) = ( ( ( ( bra ` A ) ` B ) .fn ( bra ` C ) ) ` D ) )

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    wa
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cD
    cB
    cA
    cbr
    cfv
    cfv
    #
    cC
    cbr
    cfv
    #
    chft
    co
    cfv
    #
    @5
    cD
    @6
    cfv
    cmul
    co
    #
    @4
    @5
    cc
    wcel
    #
    chil
    cc
    @6
    wf
    #
    @2
    @7
    @8
    wceq
    @0
    @9
    @3
    cA
    cB
    bracl
    adantr
    @1
    @10
    @0
    @2
    cC
    brafn
    ad2antrl
    @0
    @1
    @2
    simprr
    @5
    cD
    @6
    hfmval
    syl3anc
    eqcomd
end
