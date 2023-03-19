include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cwun.mm"
include "estrcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "wi.mm"
include "wa.mm"
include "c1.mm"
include "df-base.mm"
include "simpl.mm"
include "simpr.mm"
include "wunstr.mm"
include "ex.mm"
include "syl.mm"
include "sylbid.mm"
include "imp.mm"

theorem estrcbasbas
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cE: class E
  assume estrcbasbas.c: |- C = ( ExtStrCat ` U )
  assume estrcbasbas.b: |- B = ( Base ` C )
  assume estrcbasbas.u: |- ( ph -> U e. WUni )


  assert |- ( ( ph /\ E e. B ) -> ( Base ` E ) e. U )

  proof
    wph
    cE
    cB
    wcel
    #
    cE
    cbs
    cfv
    cU
    wcel
    #
    wph
    @0
    cE
    cU
    wcel
    #
    @1
    wph
    cB
    cU
    cE
    wph
    cU
    cC
    cbs
    cfv
    cB
    wph
    cC
    cU
    cwun
    estrcbasbas.c
    estrcbasbas.u
    estrcbas
    estrcbasbas.b
    syl6reqr
    eleq2d
    wph
    cU
    cwun
    wcel
    #
    @2
    @1
    wi
    estrcbasbas.u
    @3
    @2
    @1
    @3
    @2
    wa
    cE
    cU
    cbs
    c1
    df-base
    @3
    @2
    simpl
    @3
    @2
    simpr
    wunstr
    ex
    syl
    sylbid
    imp
end
