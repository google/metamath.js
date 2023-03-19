include "cres.mm"
include "cfv.mm"
include "cima.mm"
include "wcel.mm"
include "wceq.mm"
include "fvres.mm"
include "syl.mm"
include "fveq2d.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "jca.mm"
include "funfvima2.mm"
include "sylc.mm"
include "eqtrd.mm"

theorem resfvresima
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cH: class H
  let cX: class X
  assume resfvresima.f: |- ( ph -> Fun F )
  assume resfvresima.s: |- ( ph -> S C_ dom F )
  assume resfvresima.x: |- ( ph -> X e. S )


  assert |- ( ph -> ( ( H |` ( F " S ) ) ` ( ( F |` S ) ` X ) ) = ( H ` ( F ` X ) ) )

  proof
    wph
    cX
    cF
    cS
    cres
    cfv
    #
    cH
    cF
    cS
    cima
    #
    cres
    #
    cfv
    cX
    cF
    cfv
    #
    @2
    cfv
    #
    @3
    cH
    cfv
    #
    wph
    @0
    @3
    @2
    wph
    cX
    cS
    wcel
    #
    @0
    @3
    wceq
    resfvresima.x
    cX
    cS
    cF
    fvres
    syl
    fveq2d
    wph
    @3
    @1
    wcel
    #
    @4
    @5
    wceq
    wph
    cF
    wfun
    #
    cS
    cF
    cdm
    wss
    #
    wa
    @6
    @7
    wph
    @8
    @9
    resfvresima.f
    resfvresima.s
    jca
    resfvresima.x
    cS
    cX
    cF
    funfvima2
    sylc
    @3
    @1
    cH
    fvres
    syl
    eqtrd
end
