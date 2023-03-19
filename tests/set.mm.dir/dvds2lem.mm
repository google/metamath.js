include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "wcel.mm"
include "wb.mm"
include "divides.mm"
include "bi2anan9.mm"
include "syl2anc.mm"
include "biimpd.mm"
include "reeanv.mm"
include "syl6ibr.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "syl.mm"
include "sylibrd.mm"

theorem dvds2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vz: setvar z
  assume dvds2lem.1: |- ( ph -> ( I e. ZZ /\ J e. ZZ ) )
  assume dvds2lem.2: |- ( ph -> ( K e. ZZ /\ L e. ZZ ) )
  assume dvds2lem.3: |- ( ph -> ( M e. ZZ /\ N e. ZZ ) )
  assume dvds2lem.4: |- ( ( ph /\ ( x e. ZZ /\ y e. ZZ ) ) -> Z e. ZZ )
  assume dvds2lem.5: |- ( ( ph /\ ( x e. ZZ /\ y e. ZZ ) ) -> ( ( ( x x. I ) = J /\ ( y x. K ) = L ) -> ( Z x. M ) = N ) )

  disjoint I x
  disjoint I y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint M z
  disjoint x z
  disjoint y z
  disjoint N z
  disjoint Z z
  assert |- ( ph -> ( ( I || J /\ K || L ) -> M || N ) )

  proof
    wph
    cI
    cJ
    cdvds
    wbr
    #
    cK
    cL
    cdvds
    wbr
    #
    wa
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
    cM
    cN
    cdvds
    wbr
    #
    wph
    @2
    vx
    cv
    #
    cI
    cmul
    co
    cJ
    wceq
    #
    vy
    cv
    #
    cK
    cmul
    co
    cL
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @6
    wph
    @2
    @9
    vx
    cz
    wrex
    #
    @11
    vy
    cz
    wrex
    #
    wa
    #
    @13
    wph
    @2
    @16
    wph
    cI
    cz
    wcel
    cJ
    cz
    wcel
    wa
    #
    cK
    cz
    wcel
    cL
    cz
    wcel
    wa
    #
    @2
    @16
    wb
    dvds2lem.1
    dvds2lem.2
    @17
    @0
    @14
    @18
    @1
    @15
    vx
    cI
    cJ
    divides
    vy
    cK
    cL
    divides
    bi2anan9
    syl2anc
    biimpd
    @9
    @11
    vx
    vy
    cz
    cz
    reeanv
    syl6ibr
    wph
    @12
    @6
    vx
    vy
    cz
    cz
    wph
    @8
    cz
    wcel
    @10
    cz
    wcel
    wa
    wa
    cZ
    cz
    wcel
    @12
    cZ
    cM
    cmul
    co
    #
    cN
    wceq
    #
    @6
    dvds2lem.4
    dvds2lem.5
    @5
    @20
    vz
    cZ
    cz
    @3
    cZ
    wceq
    @4
    @19
    cN
    @3
    cZ
    cM
    cmul
    oveq1
    eqeq1d
    rspcev
    syl6an
    rexlimdvva
    syld
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    @7
    @6
    wb
    dvds2lem.3
    vz
    cM
    cN
    divides
    syl
    sylibrd
end
