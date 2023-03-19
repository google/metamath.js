include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cmul.mm"
include "1cnd.mm"
include "addcld.mm"
include "adddid.mm"
include "cc.mm"
include "wcel.mm"
include "1p1times.mm"
include "syl.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"
include "addassd.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "addcan2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "3eqtr3d.mm"
include "addcan.mm"

theorem addcomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A + B ) = ( B + A ) )

  proof
    wph
    cA
    cA
    cB
    caddc
    co
    #
    caddc
    co
    #
    cA
    cB
    cA
    caddc
    co
    #
    caddc
    co
    #
    wceq
    #
    @0
    @2
    wceq
    #
    wph
    cA
    cA
    caddc
    co
    #
    cB
    caddc
    co
    #
    @0
    cA
    caddc
    co
    #
    @1
    @3
    wph
    @7
    cB
    caddc
    co
    #
    @8
    cB
    caddc
    co
    #
    wceq
    #
    @7
    @8
    wceq
    #
    wph
    @6
    cB
    cB
    caddc
    co
    #
    caddc
    co
    #
    @0
    @0
    caddc
    co
    #
    @9
    @10
    wph
    c1
    c1
    caddc
    co
    #
    @0
    cmul
    co
    #
    @16
    cA
    cmul
    co
    #
    @16
    cB
    cmul
    co
    #
    caddc
    co
    @15
    @14
    wph
    @16
    cA
    cB
    wph
    c1
    c1
    wph
    1cnd
    #
    @20
    addcld
    muld.1
    addcomd.2
    adddid
    wph
    @0
    cc
    wcel
    #
    @17
    @15
    wceq
    wph
    cA
    cB
    muld.1
    addcomd.2
    addcld
    #
    @0
    1p1times
    syl
    wph
    @18
    @6
    @19
    @13
    caddc
    wph
    cA
    cc
    wcel
    #
    @18
    @6
    wceq
    muld.1
    cA
    1p1times
    syl
    wph
    cB
    cc
    wcel
    #
    @19
    @13
    wceq
    addcomd.2
    cB
    1p1times
    syl
    oveq12d
    3eqtr3rd
    wph
    @6
    cB
    cB
    wph
    cA
    cA
    muld.1
    muld.1
    addcld
    #
    addcomd.2
    addcomd.2
    addassd
    wph
    @0
    cA
    cB
    @22
    muld.1
    addcomd.2
    addassd
    3eqtr4d
    wph
    @7
    cc
    wcel
    @8
    cc
    wcel
    @24
    @11
    @12
    wb
    wph
    @6
    cB
    @25
    addcomd.2
    addcld
    wph
    @0
    cA
    @22
    muld.1
    addcld
    addcomd.2
    @7
    @8
    cB
    addcan2
    syl3anc
    mpbid
    wph
    cA
    cA
    cB
    muld.1
    muld.1
    addcomd.2
    addassd
    wph
    cA
    cB
    cA
    muld.1
    addcomd.2
    muld.1
    addassd
    3eqtr3d
    wph
    @23
    @21
    @2
    cc
    wcel
    @4
    @5
    wb
    muld.1
    @22
    wph
    cB
    cA
    addcomd.2
    muld.1
    addcld
    cA
    @0
    @2
    addcan
    syl3anc
    mpbid
end
