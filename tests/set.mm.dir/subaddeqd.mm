include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "oveq1d.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "pnpcan2d.mm"
include "pnpcand.mm"
include "3eqtr3d.mm"

theorem subaddeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume subaddeqd.a: |- ( ph -> A e. CC )
  assume subaddeqd.b: |- ( ph -> B e. CC )
  assume subaddeqd.c: |- ( ph -> C e. CC )
  assume subaddeqd.d: |- ( ph -> D e. CC )
  assume subaddeqd.1: |- ( ph -> ( A + B ) = ( C + D ) )


  assert |- ( ph -> ( A - D ) = ( C - B ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cD
    cB
    caddc
    co
    #
    cmin
    co
    #
    cD
    cC
    caddc
    co
    #
    @1
    cmin
    co
    #
    cA
    cD
    cmin
    co
    cC
    cB
    cmin
    co
    wph
    @2
    cC
    cD
    caddc
    co
    #
    @1
    cmin
    co
    @4
    wph
    @0
    @5
    @1
    cmin
    subaddeqd.1
    oveq1d
    wph
    @5
    @3
    @1
    cmin
    wph
    cC
    cD
    subaddeqd.c
    subaddeqd.d
    addcomd
    oveq1d
    eqtrd
    wph
    cA
    cD
    cB
    subaddeqd.a
    subaddeqd.d
    subaddeqd.b
    pnpcan2d
    wph
    cD
    cC
    cB
    subaddeqd.d
    subaddeqd.c
    subaddeqd.b
    pnpcand
    3eqtr3d
end
