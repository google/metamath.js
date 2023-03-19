include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "recnd.mm"
include "addcld.mm"
include "mulcomd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "joinlmuladdmuld.mm"

theorem int-rightdistd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-rightdistd.1: |- ( ph -> B e. RR )
  assume int-rightdistd.2: |- ( ph -> C e. RR )
  assume int-rightdistd.3: |- ( ph -> D e. RR )
  assume int-rightdistd.4: |- ( ph -> A = B )


  assert |- ( ph -> ( B x. ( C + D ) ) = ( ( A x. C ) + ( A x. D ) ) )

  proof
    wph
    cB
    cC
    cD
    caddc
    co
    #
    cmul
    co
    @0
    cB
    cmul
    co
    cA
    cC
    cmul
    co
    #
    cA
    cD
    cmul
    co
    #
    caddc
    co
    #
    wph
    cB
    @0
    wph
    cB
    int-rightdistd.1
    recnd
    #
    wph
    cC
    cD
    wph
    cC
    int-rightdistd.2
    recnd
    #
    wph
    cD
    int-rightdistd.3
    recnd
    #
    addcld
    mulcomd
    wph
    cC
    cB
    cD
    @3
    @5
    @4
    @6
    wph
    cC
    cB
    cmul
    co
    #
    @1
    cD
    cB
    cmul
    co
    #
    @2
    caddc
    wph
    @7
    cB
    cC
    cmul
    co
    @1
    wph
    cC
    cB
    @5
    @4
    mulcomd
    wph
    cB
    cA
    cC
    cmul
    wph
    cA
    cB
    int-rightdistd.4
    eqcomd
    #
    oveq1d
    eqtrd
    wph
    @8
    cB
    cD
    cmul
    co
    @2
    wph
    cD
    cB
    @6
    @4
    mulcomd
    wph
    cB
    cA
    cD
    cmul
    @9
    oveq1d
    eqtrd
    oveq12d
    joinlmuladdmuld
    eqtrd
end
