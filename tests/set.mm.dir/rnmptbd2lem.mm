include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfra1.mm"
include "nfv.mm"
include "wi.mm"
include "rspa.mm"
include "simpl.mm"
include "id.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "ex.mm"
include "syl.mm"
include "rexlimd.mm"
include "imp.mm"
include "adantll.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "reximdv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfral.mm"
include "nfan.mm"
include "simpr.mm"
include "adantlr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "simplr.mm"
include "breq2.mm"
include "rspcva.mm"
include "ralrimi.mm"
include "a1d.mm"
include "reximdva.mm"
include "impbid.mm"

theorem rnmptbd2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cV: class V
  assume rnmptbd2lem.x: |- F/ x ph
  assume rnmptbd2lem.b: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A z
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint x y
  disjoint x z
  assert |- ( ph -> ( E. y e. RR A. x e. A y <_ B <-> E. y e. RR A. z e. ran ( x e. A |-> B ) y <_ z ) )

  proof
    wph
    vy
    cv
    #
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    #
    @0
    vz
    cv
    #
    cle
    wbr
    #
    vz
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    wral
    #
    vy
    cr
    wrex
    #
    wph
    @3
    @9
    wph
    @3
    @9
    wph
    @2
    @8
    vy
    cr
    wph
    @2
    @8
    wph
    @2
    wa
    #
    @5
    vz
    @7
    @10
    @4
    @7
    wcel
    #
    @4
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @5
    @11
    @13
    @10
    @11
    @13
    @4
    cvv
    wcel
    @11
    @13
    wb
    vz
    vex
    vx
    cA
    cB
    @4
    @6
    cvv
    @6
    eqid
    #
    elrnmpt
    ax-mp
    biimpi
    adantl
    @2
    @13
    @5
    wph
    @2
    @13
    @5
    @2
    @12
    @5
    vx
    cA
    @1
    vx
    cA
    nfra1
    @5
    vx
    nfv
    #
    @2
    vx
    cv
    cA
    wcel
    #
    @12
    @5
    wi
    #
    @2
    @16
    wa
    @1
    @17
    @1
    vx
    cA
    rspa
    @1
    @12
    @5
    @1
    @12
    wa
    @0
    cB
    @4
    cle
    @1
    @12
    simpl
    @12
    cB
    @4
    wceq
    @1
    @12
    @4
    cB
    @12
    id
    eqcomd
    adantl
    breqtrd
    ex
    syl
    ex
    rexlimd
    imp
    adantll
    syldan
    ralrimiva
    ex
    reximdv
    imp
    ex
    wph
    @8
    @2
    vy
    cr
    wph
    @0
    cr
    wcel
    #
    @8
    @2
    wi
    #
    wph
    @19
    @18
    wph
    @8
    @2
    wph
    @8
    wa
    #
    @1
    vx
    cA
    wph
    @8
    vx
    rnmptbd2lem.x
    @5
    vx
    vz
    @7
    vx
    @6
    vx
    cA
    cB
    nfmpt1
    nfrn
    @15
    nfral
    nfan
    @20
    @16
    @1
    @20
    @16
    wa
    #
    cB
    @7
    wcel
    #
    @8
    @1
    @21
    @16
    cB
    cV
    wcel
    #
    @22
    @20
    @16
    simpr
    wph
    @16
    @23
    @8
    rnmptbd2lem.b
    adantlr
    vx
    cA
    cB
    @6
    cV
    @14
    elrnmpt1
    syl2anc
    wph
    @8
    @16
    simplr
    @5
    @1
    vz
    cB
    @7
    @4
    cB
    @0
    cle
    breq2
    rspcva
    syl2anc
    ex
    ralrimi
    ex
    a1d
    imp
    reximdva
    impbid
end
