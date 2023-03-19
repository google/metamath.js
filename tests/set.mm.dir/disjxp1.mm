include "cv.mm"
include "wceq.mm"
include "cxp.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "orc.mm"
include "adantl.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "csbxp.mm"
include "ineq12i.mm"
include "a1i.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "jca31.mm"
include "simpr.mm"
include "neneqd.mm"
include "disjors.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "ord.mm"
include "sylc.mm"
include "xpdisj1.mm"
include "syl.mm"
include "eqtrd.mm"
include "olc.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "ralrimivva.mm"
include "sylibr.mm"

theorem disjxp1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  assume disjxp1.1: |- ( ph -> Disj_ x e. A B )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> Disj_ x e. A ( B X. C ) )

  proof
    wph
    vy
    cv
    #
    vz
    cv
    #
    wceq
    #
    vx
    @0
    cB
    cC
    cxp
    #
    csb
    #
    vx
    @1
    @3
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    cA
    wral
    vy
    cA
    wral
    vx
    cA
    @3
    wdisj
    wph
    @8
    vy
    vz
    cA
    cA
    wph
    @0
    cA
    wcel
    #
    @1
    cA
    wcel
    #
    wa
    #
    wa
    #
    @2
    @8
    @2
    @8
    @12
    @2
    @7
    orc
    adantl
    @12
    @2
    wn
    #
    wa
    @12
    @0
    @1
    wne
    #
    @8
    @12
    @13
    simpl
    @13
    @14
    @12
    @0
    @1
    neqne
    adantl
    @12
    @14
    wa
    #
    @7
    @8
    @15
    @6
    vx
    @0
    cB
    csb
    #
    vx
    @0
    cC
    csb
    #
    cxp
    #
    vx
    @1
    cB
    csb
    #
    vx
    @1
    cC
    csb
    #
    cxp
    #
    cin
    #
    c0
    @6
    @22
    wceq
    @15
    @4
    @18
    @5
    @21
    vx
    @0
    cB
    cC
    csbxp
    vx
    @1
    cB
    cC
    csbxp
    ineq12i
    a1i
    @15
    @16
    @19
    cin
    c0
    wceq
    #
    @22
    c0
    wceq
    @15
    wph
    @9
    wa
    #
    @10
    wa
    #
    @13
    @23
    @15
    wph
    @9
    @10
    wph
    @11
    @14
    simpll
    wph
    @9
    @10
    @14
    simplrl
    wph
    @9
    @10
    @14
    simplrr
    jca31
    @15
    @0
    @1
    @12
    @14
    simpr
    neneqd
    @25
    @2
    @23
    @24
    @2
    @23
    wo
    #
    vz
    cA
    wph
    @26
    vz
    cA
    wral
    #
    vy
    cA
    wph
    vx
    cA
    cB
    wdisj
    @27
    vy
    cA
    wral
    disjxp1.1
    vx
    cA
    cB
    vy
    vz
    disjors
    sylib
    r19.21bi
    r19.21bi
    ord
    sylc
    @16
    @19
    @17
    @20
    xpdisj1
    syl
    eqtrd
    @7
    @2
    olc
    syl
    syl2anc
    pm2.61dan
    ralrimivva
    vx
    cA
    @3
    vy
    vz
    disjors
    sylibr
end
