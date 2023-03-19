include "wf.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "ringcbasbasALTV.mm"
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

theorem funcringcsetclem3ALTV
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cX: class X
  let vk: setvar k
  assume funcringcsetcALTV.r: |- R = ( RingCatALTV ` U )
  assume funcringcsetcALTV.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV.b: |- B = ( Base ` R )
  assume funcringcsetcALTV.c: |- C = ( Base ` S )
  assume funcringcsetcALTV.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )

  disjoint B x
  disjoint ph x
  disjoint C x
  disjoint X x
  disjoint k x
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
    cR
    @0
    cU
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    funcringcsetcALTV.u
    ringcbasbasALTV
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
    funcringcsetcALTV.s
    funcringcsetcALTV.u
    setcbas
    eqcomd
    adantr
    eleqtrrd
    funcringcsetcALTV.c
    syl6eleqr
    @2
    eqid
    fmptd
    wph
    cB
    cC
    cF
    @2
    funcringcsetcALTV.f
    feq1d
    mpbird
end
