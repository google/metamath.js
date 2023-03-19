include "wf.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "estrcbasbas.mm"
include "wceq.mm"
include "cwun.mm"
include "setcbas.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "syl6eleqr.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem funcestrcsetclem3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cX: class X
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )

  disjoint B x
  disjoint ph x
  disjoint C x
  disjoint X x
  assert |- ( ph -> F : B --> C )

  proof
    wph
    cB
    cC
    cF
    wf
    cB
    cC
    vx
    cB
    vx
    cv
    #
    cbs
    cfv
    #
    cmpt
    #
    wf
    wph
    vx
    cB
    @1
    cC
    @2
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @1
    cS
    cbs
    cfv
    #
    cC
    @4
    @1
    cU
    @5
    wph
    cB
    cE
    cU
    @0
    funcestrcsetc.e
    funcestrcsetc.b
    funcestrcsetc.u
    estrcbasbas
    wph
    @5
    cU
    wceq
    @3
    wph
    cU
    @5
    wph
    cS
    cU
    cwun
    funcestrcsetc.s
    funcestrcsetc.u
    setcbas
    eqcomd
    adantr
    eleqtrrd
    funcestrcsetc.c
    syl6eleqr
    @2
    eqid
    fmptd
    wph
    cB
    cC
    cF
    @2
    funcestrcsetc.f
    feq1d
    mpbird
end
