include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "wa.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfrex.mm"
include "nfan.mm"
include "simpr.mm"
include "rnmptbdd.mm"
include "ex.mm"
include "wi.mm"
include "wcel.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfv.mm"
include "nfral.mm"
include "adantlr.mm"
include "eqid.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "simplr.mm"
include "breq1.mm"
include "rspcva.mm"
include "ralrimi.mm"
include "a1d.mm"
include "reximdai.mm"
include "impbid.mm"

theorem rnmptbdlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cV: class V
  assume rnmptbdlem.x: |- F/ x ph
  assume rnmptbdlem.y: |- F/ y ph
  assume rnmptbdlem.b: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  assert |- ( ph -> ( E. y e. RR A. x e. A B <_ y <-> E. y e. RR A. z e. ran ( x e. A |-> B ) z <_ y ) )

  proof
    wph
    cB
    vy
    cv
    #
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
    vz
    cv
    #
    @0
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
    wa
    vx
    vy
    vz
    cA
    cB
    wph
    @3
    vx
    rnmptbdlem.x
    @2
    vx
    vy
    cr
    vx
    cr
    nfcv
    @1
    vx
    cA
    nfra1
    nfrex
    nfan
    wph
    @3
    simpr
    rnmptbdd
    ex
    wph
    @8
    @2
    vy
    cr
    rnmptbdlem.y
    wph
    @8
    @2
    wi
    @0
    cr
    wcel
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
    rnmptbdlem.x
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
    @5
    vx
    nfv
    nfral
    nfan
    @10
    vx
    cv
    cA
    wcel
    #
    @1
    @10
    @11
    wa
    #
    cB
    @7
    wcel
    #
    @8
    @1
    @12
    @11
    cB
    cV
    wcel
    #
    @13
    @10
    @11
    simpr
    wph
    @11
    @14
    @8
    rnmptbdlem.b
    adantlr
    vx
    cA
    cB
    @6
    cV
    @6
    eqid
    elrnmpt1
    syl2anc
    wph
    @8
    @11
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
    breq1
    rspcva
    syl2anc
    ex
    ralrimi
    ex
    a1d
    reximdai
    impbid
end
