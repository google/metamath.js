include "co.mm"
include "cop.mm"
include "cfv.mm"
include "cxp.mm"
include "cima.mm"
include "df-ov.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "sseldd.mm"
include "funfvima.mm"
include "mpd.mm"
include "syl5eqel.mm"

theorem elovimad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume elovimad.1: |- ( ph -> A e. C )
  assume elovimad.2: |- ( ph -> B e. D )
  assume elovimad.3: |- ( ph -> Fun F )
  assume elovimad.4: |- ( ph -> ( C X. D ) C_ dom F )


  assert |- ( ph -> ( A F B ) e. ( F " ( C X. D ) ) )

  proof
    wph
    cA
    cB
    cF
    co
    cA
    cB
    cop
    #
    cF
    cfv
    #
    cF
    cC
    cD
    cxp
    #
    cima
    #
    cA
    cB
    cF
    df-ov
    wph
    @0
    @2
    wcel
    #
    @1
    @3
    wcel
    #
    wph
    cA
    cC
    wcel
    cB
    cD
    wcel
    @4
    elovimad.1
    elovimad.2
    cA
    cB
    cC
    cD
    opelxpi
    syl2anc
    #
    wph
    cF
    wfun
    @0
    cF
    cdm
    #
    wcel
    @4
    @5
    wi
    elovimad.3
    wph
    @2
    @7
    @0
    elovimad.4
    @6
    sseldd
    @2
    @0
    cF
    funfvima
    syl2anc
    mpd
    syl5eqel
end
