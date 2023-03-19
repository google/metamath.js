include "cvoln.mm"
include "cfv.mm"
include "covoln.mm"
include "ccaragen.mm"
include "cres.mm"
include "vonval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cdm.mm"
include "dmvon.mm"
include "eleqtrd.mm"
include "fvres.mm"
include "syl.mm"
include "eqtrd.mm"

theorem mblvon
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume mblvon.1: |- ( ph -> X e. Fin )
  assume mblvon.2: |- ( ph -> A e. dom ( voln ` X ) )


  assert |- ( ph -> ( ( voln ` X ) ` A ) = ( ( voln* ` X ) ` A ) )

  proof
    wph
    cA
    cX
    cvoln
    cfv
    #
    cfv
    cA
    cX
    covoln
    cfv
    #
    @1
    ccaragen
    cfv
    #
    cres
    #
    cfv
    #
    cA
    @1
    cfv
    #
    wph
    cA
    @0
    @3
    wph
    cX
    mblvon.1
    vonval
    fveq1d
    wph
    cA
    @2
    wcel
    @4
    @5
    wceq
    wph
    cA
    @0
    cdm
    @2
    mblvon.2
    wph
    cX
    mblvon.1
    dmvon
    eleqtrd
    cA
    @2
    @1
    fvres
    syl
    eqtrd
end
