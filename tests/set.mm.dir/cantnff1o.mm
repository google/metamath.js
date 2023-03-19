include "coe.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "cep.mm"
include "ccnf.mm"
include "wiso.mm"
include "wf1o.mm"
include "eqid.mm"
include "cantnf.mm"
include "isof1o.mm"
include "syl.mm"

theorem cantnff1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cantnff1o.1: |- S = dom ( A CNF B )
  assume cantnff1o.2: |- ( ph -> A e. On )
  assume cantnff1o.3: |- ( ph -> B e. On )


  assert |- ( ph -> ( A CNF B ) : S -1-1-onto-> ( A ^o B ) )

  proof
    wph
    cS
    cA
    cB
    coe
    co
    #
    vz
    cv
    #
    vx
    cv
    #
    cfv
    @1
    vy
    cv
    #
    cfv
    wcel
    @1
    vw
    cv
    #
    wcel
    @4
    @2
    cfv
    @4
    @3
    cfv
    wceq
    wi
    vw
    cB
    wral
    wa
    vz
    cB
    wrex
    vx
    vy
    copab
    #
    cep
    cA
    cB
    ccnf
    co
    #
    wiso
    cS
    @0
    @6
    wf1o
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cS
    @5
    cantnff1o.1
    cantnff1o.2
    cantnff1o.3
    @5
    eqid
    cantnf
    cS
    @0
    @5
    cep
    @6
    isof1o
    syl
end
