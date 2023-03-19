include "csn.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "elsni.mm"
include "fveq2d.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "elmapd.mm"
include "mpbird.mm"

theorem elmapsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume elmapsnd.1: |- ( ph -> F Fn { A } )
  assume elmapsnd.2: |- ( ph -> B e. V )
  assume elmapsnd.3: |- ( ph -> ( F ` A ) e. B )


  assert |- ( ph -> F e. ( B ^m { A } ) )

  proof
    wph
    cF
    cB
    cA
    csn
    #
    cmap
    co
    wcel
    @0
    cB
    cF
    wf
    #
    wph
    cF
    @0
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vx
    @0
    wral
    #
    wa
    @1
    wph
    @2
    @6
    elmapsnd.1
    wph
    @5
    vx
    @0
    wph
    @3
    @0
    wcel
    #
    wa
    @4
    cA
    cF
    cfv
    #
    cB
    @7
    @4
    @8
    wceq
    wph
    @7
    @3
    cA
    cF
    @3
    cA
    elsni
    fveq2d
    adantl
    wph
    @8
    cB
    wcel
    @7
    elmapsnd.3
    adantr
    eqeltrd
    ralrimiva
    jca
    vx
    @0
    cB
    cF
    ffnfv
    sylibr
    wph
    cB
    @0
    cF
    cV
    cvv
    elmapsnd.2
    @0
    cvv
    wcel
    wph
    cA
    snex
    a1i
    elmapd
    mpbird
end
