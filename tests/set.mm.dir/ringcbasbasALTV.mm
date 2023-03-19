include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "crg.mm"
include "cin.mm"
include "cwun.mm"
include "ringcbasALTV.mm"
include "eleq2d.mm"
include "wa.mm"
include "wi.mm"
include "elin.mm"
include "c1.mm"
include "df-base.mm"
include "simpl.mm"
include "simpr.mm"
include "wunstr.mm"
include "ex.mm"
include "syl11.mm"
include "adantr.mm"
include "sylbi.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"

theorem ringcbasbasALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  let vk: setvar k
  let vx: setvar x
  assume ringcbasbasALTV.r: |- C = ( RingCatALTV ` U )
  assume ringcbasbasALTV.b: |- B = ( Base ` C )
  assume ringcbasbasALTV.u: |- ( ph -> U e. WUni )


  assert |- ( ( ph /\ R e. B ) -> ( Base ` R ) e. U )

  proof
    wph
    cR
    cB
    wcel
    #
    cR
    cbs
    cfv
    cU
    wcel
    #
    wph
    @0
    cR
    cU
    crg
    cin
    #
    wcel
    #
    @1
    wph
    cB
    @2
    cR
    wph
    cB
    cC
    cU
    cwun
    ringcbasbasALTV.r
    ringcbasbasALTV.b
    ringcbasbasALTV.u
    ringcbasALTV
    eleq2d
    @3
    wph
    @1
    @3
    cR
    cU
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    wph
    @1
    wi
    #
    cR
    cU
    crg
    elin
    @4
    @6
    @5
    cU
    cwun
    wcel
    #
    @4
    @1
    wph
    @7
    @4
    @1
    @7
    @4
    wa
    cR
    cU
    cbs
    c1
    df-base
    @7
    @4
    simpl
    @7
    @4
    simpr
    wunstr
    ex
    ringcbasbasALTV.u
    syl11
    adantr
    sylbi
    com12
    sylbid
    imp
end
