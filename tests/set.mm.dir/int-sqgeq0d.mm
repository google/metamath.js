include "cc0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cle.mm"
include "sqge0d.mm"
include "oveq1d.mm"
include "recnd.mm"
include "sqvald.mm"
include "wceq.mm"
include "wi.mm"
include "eqcom.mm"
include "imbi2i.mm"
include "mpbi.mm"
include "eqtrd.mm"
include "breqtrd.mm"

theorem int-sqgeq0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-sqgeq0d.1: |- ( ph -> A e. RR )
  assume int-sqgeq0d.2: |- ( ph -> B e. RR )
  assume int-sqgeq0d.3: |- ( ph -> A = B )


  assert |- ( ph -> 0 <_ ( A x. B ) )

  proof
    wph
    cc0
    cA
    c2
    cexp
    co
    #
    cA
    cB
    cmul
    co
    #
    cle
    wph
    cA
    int-sqgeq0d.1
    sqge0d
    wph
    @0
    cB
    c2
    cexp
    co
    #
    @1
    wph
    cA
    cB
    c2
    cexp
    int-sqgeq0d.3
    oveq1d
    wph
    @2
    cB
    cB
    cmul
    co
    @1
    wph
    cB
    wph
    cB
    int-sqgeq0d.2
    recnd
    sqvald
    wph
    cB
    cA
    cB
    cmul
    wph
    cA
    cB
    wceq
    #
    wi
    wph
    cB
    cA
    wceq
    #
    wi
    int-sqgeq0d.3
    @3
    @4
    wph
    cA
    cB
    eqcom
    imbi2i
    mpbi
    oveq1d
    eqtrd
    eqtrd
    breqtrd
end
