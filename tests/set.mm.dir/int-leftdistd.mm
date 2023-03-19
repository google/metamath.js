include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "recnd.mm"
include "adddird.mm"
include "mulcld.mm"
include "addcomd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem int-leftdistd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-leftdistd.1: |- ( ph -> B e. RR )
  assume int-leftdistd.2: |- ( ph -> C e. RR )
  assume int-leftdistd.3: |- ( ph -> D e. RR )
  assume int-leftdistd.4: |- ( ph -> A = B )


  assert |- ( ph -> ( ( C + D ) x. B ) = ( ( C x. A ) + ( D x. A ) ) )

  proof
    wph
    cC
    cD
    caddc
    co
    cB
    cmul
    co
    cC
    cB
    cmul
    co
    #
    cD
    cB
    cmul
    co
    #
    caddc
    co
    #
    @1
    @0
    caddc
    co
    #
    cC
    cA
    cmul
    co
    #
    cD
    cA
    cmul
    co
    #
    caddc
    co
    #
    wph
    cC
    cD
    cB
    wph
    cC
    int-leftdistd.2
    recnd
    #
    wph
    cD
    int-leftdistd.3
    recnd
    #
    wph
    cB
    int-leftdistd.1
    recnd
    #
    adddird
    wph
    @0
    @1
    wph
    cC
    cB
    @7
    @9
    mulcld
    #
    wph
    cD
    cB
    @8
    @9
    mulcld
    #
    addcomd
    wph
    @3
    @2
    @6
    wph
    @1
    @0
    @11
    @10
    addcomd
    wph
    @0
    @4
    @1
    @5
    caddc
    wph
    cB
    cA
    cC
    cmul
    wph
    cA
    cB
    int-leftdistd.4
    eqcomd
    #
    oveq2d
    wph
    cB
    cA
    cD
    cmul
    @12
    oveq2d
    oveq12d
    eqtrd
    3eqtrd
end
