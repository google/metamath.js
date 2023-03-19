include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cdvds.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "wb.mm"
include "divides.mm"
include "syl.mm"
include "3imtr4d.mm"

theorem dvds1lem
  let wph: wff ph
  let vx: setvar x
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vz: setvar z
  assume dvds1lem.1: |- ( ph -> ( J e. ZZ /\ K e. ZZ ) )
  assume dvds1lem.2: |- ( ph -> ( M e. ZZ /\ N e. ZZ ) )
  assume dvds1lem.3: |- ( ( ph /\ x e. ZZ ) -> Z e. ZZ )
  assume dvds1lem.4: |- ( ( ph /\ x e. ZZ ) -> ( ( x x. J ) = K -> ( Z x. M ) = N ) )

  disjoint J x
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint M z
  disjoint x z
  disjoint N z
  disjoint Z z
  assert |- ( ph -> ( J || K -> M || N ) )

  proof
    wph
    vx
    cv
    #
    cJ
    cmul
    co
    cK
    wceq
    #
    vx
    cz
    wrex
    #
    vz
    cv
    #
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vz
    cz
    wrex
    #
    cJ
    cK
    cdvds
    wbr
    #
    cM
    cN
    cdvds
    wbr
    #
    wph
    @1
    @6
    vx
    cz
    wph
    @0
    cz
    wcel
    wa
    cZ
    cz
    wcel
    @1
    cZ
    cM
    cmul
    co
    #
    cN
    wceq
    #
    @6
    dvds1lem.3
    dvds1lem.4
    @5
    @10
    vz
    cZ
    cz
    @3
    cZ
    wceq
    @4
    @9
    cN
    @3
    cZ
    cM
    cmul
    oveq1
    eqeq1d
    rspcev
    syl6an
    rexlimdva
    wph
    cJ
    cz
    wcel
    cK
    cz
    wcel
    wa
    @7
    @2
    wb
    dvds1lem.1
    vx
    cJ
    cK
    divides
    syl
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    @8
    @6
    wb
    dvds1lem.2
    vz
    cM
    cN
    divides
    syl
    3imtr4d
end
