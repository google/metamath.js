include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "oveq1d.mm"
include "recnd.mm"
include "sqvald.mm"
include "wceq.mm"
include "wi.mm"
include "eqcom.mm"
include "imbi2i.mm"
include "mpbi.mm"
include "eqtrd.mm"
include "eqcomd.mm"

theorem int-sqdefd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-sqdefd.1: |- ( ph -> B e. RR )
  assume int-sqdefd.2: |- ( ph -> A = B )


  assert |- ( ph -> ( A x. B ) = ( A ^ 2 ) )

  proof
    wph
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
    int-sqdefd.2
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
    int-sqdefd.1
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
    int-sqdefd.2
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
    eqcomd
end
