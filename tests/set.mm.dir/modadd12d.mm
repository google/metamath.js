include "caddc.mm"
include "co.mm"
include "cmo.mm"
include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wceq.mm"
include "modadd1.mm"
include "syl221anc.mm"
include "recnd.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem modadd12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume modadd12d.1: |- ( ph -> A e. RR )
  assume modadd12d.2: |- ( ph -> B e. RR )
  assume modadd12d.3: |- ( ph -> C e. RR )
  assume modadd12d.4: |- ( ph -> D e. RR )
  assume modadd12d.5: |- ( ph -> E e. RR+ )
  assume modadd12d.6: |- ( ph -> ( A mod E ) = ( B mod E ) )
  assume modadd12d.7: |- ( ph -> ( C mod E ) = ( D mod E ) )


  assert |- ( ph -> ( ( A + C ) mod E ) = ( ( B + D ) mod E ) )

  proof
    wph
    cA
    cC
    caddc
    co
    cE
    cmo
    co
    #
    cB
    cC
    caddc
    co
    #
    cE
    cmo
    co
    #
    cB
    cD
    caddc
    co
    #
    cE
    cmo
    co
    #
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cE
    crp
    wcel
    #
    cA
    cE
    cmo
    co
    cB
    cE
    cmo
    co
    wceq
    @0
    @2
    wceq
    modadd12d.1
    modadd12d.2
    modadd12d.3
    modadd12d.5
    modadd12d.6
    cA
    cB
    cC
    cE
    modadd1
    syl221anc
    wph
    @2
    cC
    cB
    caddc
    co
    #
    cE
    cmo
    co
    #
    cD
    cB
    caddc
    co
    #
    cE
    cmo
    co
    #
    @4
    wph
    @1
    @8
    cE
    cmo
    wph
    cB
    cC
    wph
    cB
    modadd12d.2
    recnd
    #
    wph
    cC
    modadd12d.3
    recnd
    addcomd
    oveq1d
    wph
    @6
    cD
    cr
    wcel
    @5
    @7
    cC
    cE
    cmo
    co
    cD
    cE
    cmo
    co
    wceq
    @9
    @11
    wceq
    modadd12d.3
    modadd12d.4
    modadd12d.2
    modadd12d.5
    modadd12d.7
    cC
    cD
    cB
    cE
    modadd1
    syl221anc
    wph
    @10
    @3
    cE
    cmo
    wph
    cD
    cB
    wph
    cD
    modadd12d.4
    recnd
    @12
    addcomd
    oveq1d
    3eqtrd
    eqtrd
end
