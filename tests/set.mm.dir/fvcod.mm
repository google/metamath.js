include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "fveq1i.mm"
include "a1i.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "fvco.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem fvcod
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  assume fvcod.g: |- ( ph -> Fun G )
  assume fvcod.a: |- ( ph -> A e. dom G )
  assume fvcod.h: |- H = ( F o. G )


  assert |- ( ph -> ( H ` A ) = ( F ` ( G ` A ) ) )

  proof
    wph
    cA
    cH
    cfv
    #
    cA
    cF
    cG
    ccom
    #
    cfv
    #
    cA
    cG
    cfv
    cF
    cfv
    #
    @0
    @2
    wceq
    wph
    cA
    cH
    @1
    fvcod.h
    fveq1i
    a1i
    wph
    cG
    wfun
    cA
    cG
    cdm
    wcel
    @2
    @3
    wceq
    fvcod.g
    fvcod.a
    cA
    cF
    cG
    fvco
    syl2anc
    eqtrd
end
