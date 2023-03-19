include "cv.mm"
include "covoln.mm"
include "cfv.mm"
include "ccaragen.mm"
include "cres.mm"
include "cfn.mm"
include "cvoln.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-voln.mm"
include "a1i.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "reseq12d.mm"
include "adantl.mm"
include "wcel.mm"
include "fvex.mm"
include "resex.mm"
include "fvmptd.mm"

theorem vonval
  let wph: wff ph
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume vonval.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( voln ` X ) = ( ( voln* ` X ) |` ( CaraGen ` ( voln* ` X ) ) ) )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    covoln
    cfv
    #
    @1
    ccaragen
    cfv
    #
    cres
    #
    cX
    covoln
    cfv
    #
    @4
    ccaragen
    cfv
    #
    cres
    #
    cfn
    cvoln
    cvv
    cvoln
    vx
    cfn
    @3
    cmpt
    wceq
    wph
    vx
    df-voln
    a1i
    @0
    cX
    wceq
    #
    @3
    @6
    wceq
    wph
    @7
    @1
    @4
    @2
    @5
    @0
    cX
    covoln
    fveq2
    #
    @7
    @1
    @4
    ccaragen
    @8
    fveq2d
    reseq12d
    adantl
    vonval.1
    @6
    cvv
    wcel
    wph
    @4
    @5
    cX
    covoln
    fvex
    resex
    a1i
    fvmptd
end
