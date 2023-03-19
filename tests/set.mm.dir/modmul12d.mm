include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "crp.mm"
include "wceq.mm"
include "zred.mm"
include "modmul1.mm"
include "syl221anc.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem modmul12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume modmul12d.1: |- ( ph -> A e. ZZ )
  assume modmul12d.2: |- ( ph -> B e. ZZ )
  assume modmul12d.3: |- ( ph -> C e. ZZ )
  assume modmul12d.4: |- ( ph -> D e. ZZ )
  assume modmul12d.5: |- ( ph -> E e. RR+ )
  assume modmul12d.6: |- ( ph -> ( A mod E ) = ( B mod E ) )
  assume modmul12d.7: |- ( ph -> ( C mod E ) = ( D mod E ) )


  assert |- ( ph -> ( ( A x. C ) mod E ) = ( ( B x. D ) mod E ) )

  proof
    wph
    cA
    cC
    cmul
    co
    cE
    cmo
    co
    #
    cB
    cC
    cmul
    co
    #
    cE
    cmo
    co
    #
    cB
    cD
    cmul
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
    cC
    cz
    wcel
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
    wph
    cA
    modmul12d.1
    zred
    wph
    cB
    modmul12d.2
    zred
    modmul12d.3
    modmul12d.5
    modmul12d.6
    cA
    cB
    cC
    cE
    modmul1
    syl221anc
    wph
    @2
    cC
    cB
    cmul
    co
    #
    cE
    cmo
    co
    #
    cD
    cB
    cmul
    co
    #
    cE
    cmo
    co
    #
    @4
    wph
    @1
    @6
    cE
    cmo
    wph
    cB
    cC
    wph
    cB
    modmul12d.2
    zcnd
    #
    wph
    cC
    modmul12d.3
    zcnd
    mulcomd
    oveq1d
    wph
    cC
    cr
    wcel
    cD
    cr
    wcel
    cB
    cz
    wcel
    @5
    cC
    cE
    cmo
    co
    cD
    cE
    cmo
    co
    wceq
    @7
    @9
    wceq
    wph
    cC
    modmul12d.3
    zred
    wph
    cD
    modmul12d.4
    zred
    modmul12d.2
    modmul12d.5
    modmul12d.7
    cC
    cD
    cB
    cE
    modmul1
    syl221anc
    wph
    @8
    @3
    cE
    cmo
    wph
    cD
    cB
    wph
    cD
    modmul12d.4
    zcnd
    @10
    mulcomd
    oveq1d
    3eqtrd
    eqtrd
end
