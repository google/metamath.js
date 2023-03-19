include "cc.mm"
include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "wral.mm"
include "ssun2.mm"
include "wb.mm"
include "simpl3.mm"
include "snssg.mm"
include "syl.mm"
include "mpbiri.mm"
include "ctopon.mm"
include "crest.mm"
include "cnfldtopon.mm"
include "simpl2.mm"
include "snssd.mm"
include "unssd.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "a1i.mm"
include "simpr.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "iftrue.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "ex.mm"

theorem limcvallem
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume limcval.j: |- J = ( K |`t ( A u. { B } ) )
  assume limcval.k: |- K = ( TopOpen ` CCfld )
  assume limcvallem.g: |- G = ( z e. ( A u. { B } ) |-> if ( z = B , C , ( F ` z ) ) )

  disjoint A z
  disjoint B z
  disjoint F z
  disjoint K z
  disjoint C z
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B f
  disjoint B j
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F j
  disjoint F x
  disjoint F y
  disjoint K f
  disjoint K j
  disjoint K x
  disjoint K y
  disjoint C y
  disjoint G y
  disjoint J f
  disjoint J j
  disjoint J x
  disjoint J y
  assert |- ( ( F : A --> CC /\ A C_ CC /\ B e. CC ) -> ( G e. ( ( J CnP K ) ` B ) -> C e. CC ) )

  proof
    cA
    cc
    cF
    wf
    #
    cA
    cc
    wss
    #
    cB
    cc
    wcel
    #
    w3a
    #
    cG
    cB
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cC
    cc
    wcel
    #
    @3
    @4
    wa
    #
    cB
    cA
    cB
    csn
    #
    cun
    #
    wcel
    #
    vz
    cv
    #
    cB
    wceq
    #
    cC
    @10
    cF
    cfv
    #
    cif
    #
    cc
    wcel
    #
    vz
    @8
    wral
    #
    @5
    @6
    @9
    @7
    @8
    wss
    #
    @7
    cA
    ssun2
    @6
    @2
    @9
    @16
    wb
    @0
    @1
    @2
    @4
    simpl3
    #
    cB
    @8
    cc
    snssg
    syl
    mpbiri
    @6
    @8
    cc
    cG
    wf
    #
    @15
    @6
    cJ
    @8
    ctopon
    cfv
    #
    wcel
    cK
    cc
    ctopon
    cfv
    wcel
    #
    @4
    @18
    @6
    cJ
    cK
    @8
    crest
    co
    #
    @19
    limcval.j
    @6
    @20
    @8
    cc
    wss
    @21
    @19
    wcel
    cK
    limcval.k
    cnfldtopon
    #
    @6
    cA
    @7
    cc
    @0
    @1
    @2
    @4
    simpl2
    @6
    cB
    cc
    @17
    snssd
    unssd
    @8
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    @20
    @6
    @22
    a1i
    @3
    @4
    simpr
    cB
    cG
    cJ
    cK
    @8
    cc
    cnpf2
    syl3anc
    vz
    @8
    cc
    @13
    cG
    limcvallem.g
    fmpt
    sylibr
    @14
    @5
    vz
    cB
    @8
    @11
    @13
    cC
    cc
    @11
    cC
    @12
    iftrue
    eleq1d
    rspcv
    sylc
    ex
end
