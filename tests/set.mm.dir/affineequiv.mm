include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "mulcld.mm"
include "subsubd.mm"
include "subcld.mm"
include "addcomd.mm"
include "eqtr2d.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "addsubassd.mm"
include "pncan3d.mm"
include "subdid.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"
include "eqeq2d.mm"
include "addid1d.mm"
include "eqeq1d.mm"
include "0cnd.mm"
include "addcand.mm"
include "3bitr2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "subeq0ad.mm"
include "bitrd.mm"

theorem affineequiv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume affineequiv.A: |- ( ph -> A e. CC )
  assume affineequiv.B: |- ( ph -> B e. CC )
  assume affineequiv.C: |- ( ph -> C e. CC )
  assume affineequiv.D: |- ( ph -> D e. CC )


  assert |- ( ph -> ( B = ( ( D x. A ) + ( ( 1 - D ) x. C ) ) <-> ( C - B ) = ( D x. ( C - A ) ) ) )

  proof
    wph
    cB
    cD
    cA
    cmul
    co
    #
    c1
    cD
    cmin
    co
    cC
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    cC
    cB
    cmin
    co
    #
    cD
    cC
    cA
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @4
    @6
    wceq
    wph
    @3
    cc0
    @7
    wceq
    #
    @8
    wph
    @3
    cB
    cB
    @7
    caddc
    co
    #
    wceq
    cB
    cc0
    caddc
    co
    #
    @10
    wceq
    @9
    wph
    @2
    @10
    cB
    wph
    @0
    cC
    cD
    cC
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cC
    @12
    @0
    cmin
    co
    #
    cmin
    co
    #
    @2
    @10
    wph
    @16
    @13
    @0
    caddc
    co
    @14
    wph
    cC
    @12
    @0
    affineequiv.C
    wph
    cD
    cC
    affineequiv.D
    affineequiv.C
    mulcld
    #
    wph
    cD
    cA
    affineequiv.D
    affineequiv.A
    mulcld
    #
    subsubd
    wph
    @13
    @0
    wph
    cC
    @12
    affineequiv.C
    @17
    subcld
    @18
    addcomd
    eqtr2d
    wph
    @1
    @13
    @0
    caddc
    wph
    @1
    c1
    cC
    cmul
    co
    #
    @12
    cmin
    co
    @13
    wph
    c1
    cD
    cC
    wph
    1cnd
    affineequiv.D
    affineequiv.C
    subdird
    wph
    @19
    cC
    @12
    cmin
    wph
    cC
    affineequiv.C
    mulid2d
    oveq1d
    eqtrd
    oveq2d
    wph
    cB
    @4
    caddc
    co
    #
    @6
    cmin
    co
    @10
    @16
    wph
    cB
    @4
    @6
    affineequiv.B
    wph
    cC
    cB
    affineequiv.C
    affineequiv.B
    subcld
    #
    wph
    cD
    @5
    affineequiv.D
    wph
    cC
    cA
    affineequiv.C
    affineequiv.A
    subcld
    mulcld
    #
    addsubassd
    wph
    @20
    cC
    @6
    @15
    cmin
    wph
    cB
    cC
    affineequiv.B
    affineequiv.C
    pncan3d
    wph
    cD
    cC
    cA
    affineequiv.D
    affineequiv.C
    affineequiv.A
    subdid
    oveq12d
    eqtr3d
    3eqtr4d
    eqeq2d
    wph
    @11
    cB
    @10
    wph
    cB
    affineequiv.B
    addid1d
    eqeq1d
    wph
    cB
    cc0
    @7
    affineequiv.B
    wph
    0cnd
    wph
    @4
    @6
    @21
    @22
    subcld
    addcand
    3bitr2d
    cc0
    @7
    eqcom
    syl6bb
    wph
    @4
    @6
    @21
    @22
    subeq0ad
    bitrd
end
