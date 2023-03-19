include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cva.mm"
include "caddc.mm"
include "hstosum.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "chil.mm"
include "csp.mm"
include "cc0.mm"
include "wceq.mm"
include "hstcl.mm"
include "adantr.mm"
include "ad2ant2r.mm"
include "hstorth.mm"
include "normpyth.mm"
include "3impia.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem hstpyth
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( ( ( S e. CHStates /\ A e. CH ) /\ ( B e. CH /\ A C_ ( _|_ ` B ) ) ) -> ( ( normh ` ( S ` ( A vH B ) ) ) ^ 2 ) = ( ( ( normh ` ( S ` A ) ) ^ 2 ) + ( ( normh ` ( S ` B ) ) ^ 2 ) ) )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    #
    cB
    cch
    wcel
    #
    cA
    cB
    cort
    cfv
    wss
    #
    wa
    #
    wa
    #
    cA
    cB
    chj
    co
    cS
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @9
    cno
    cfv
    c2
    cexp
    co
    @10
    cno
    cfv
    c2
    cexp
    co
    caddc
    co
    #
    @6
    @8
    @12
    c2
    cexp
    @6
    @7
    @11
    cno
    cA
    cB
    cS
    hstosum
    fveq2d
    oveq1d
    @6
    @9
    chil
    wcel
    #
    @10
    chil
    wcel
    #
    @9
    @10
    csp
    co
    cc0
    wceq
    #
    @13
    @14
    wceq
    #
    @2
    @15
    @5
    cA
    cS
    hstcl
    adantr
    @0
    @3
    @16
    @1
    @4
    cB
    cS
    hstcl
    ad2ant2r
    cA
    cB
    cS
    hstorth
    @15
    @16
    @17
    @18
    @9
    @10
    normpyth
    3impia
    syl3anc
    eqtrd
end
