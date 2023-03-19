include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cbr.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
include "cc.mm"
include "wceq.mm"
include "bracl.mm"
include "mulcom.mm"
include "syl2an.mm"
include "clf.mm"
include "bralnfn.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "simplr.mm"
include "lnfnmul.mm"
include "syl3anc.mm"
include "eqtr4d.mm"

theorem kbass4
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


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( ( bra ` A ) ` B ) x. ( ( bra ` C ) ` D ) ) = ( ( bra ` A ) ` ( ( ( bra ` C ) ` D ) .h B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cC
    chil
    wcel
    cD
    chil
    wcel
    wa
    #
    wa
    #
    cB
    cA
    cbr
    cfv
    #
    cfv
    #
    cD
    cC
    cbr
    cfv
    cfv
    #
    cmul
    co
    #
    @7
    @6
    cmul
    co
    #
    @7
    cB
    csm
    co
    @5
    cfv
    #
    @2
    @6
    cc
    wcel
    @7
    cc
    wcel
    #
    @8
    @9
    wceq
    @3
    cA
    cB
    bracl
    cC
    cD
    bracl
    #
    @6
    @7
    mulcom
    syl2an
    @4
    @5
    clf
    wcel
    #
    @11
    @1
    @10
    @9
    wceq
    @0
    @13
    @1
    @3
    cA
    bralnfn
    ad2antrr
    @3
    @11
    @2
    @12
    adantl
    @0
    @1
    @3
    simplr
    @7
    cB
    @5
    lnfnmul
    syl3anc
    eqtr4d
end
