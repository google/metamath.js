include "cyon.mm"
include "cfv.mm"
include "cop.mm"
include "ccurf.mm"
include "co.mm"
include "cv.mm"
include "coppc.mm"
include "chof.mm"
include "ccat.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-yon.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem yonval
  let wph: wff ph
  let cC: class C
  let cM: class M
  let cO: class O
  let cY: class Y
  let vc: setvar c
  assume yonval.y: |- Y = ( Yon ` C )
  assume yonval.c: |- ( ph -> C e. Cat )
  assume yonval.o: |- O = ( oppCat ` C )
  assume yonval.m: |- M = ( HomF ` O )


  assert |- ( ph -> Y = ( <. C , O >. curryF M ) )

  proof
    wph
    cY
    cC
    cyon
    cfv
    cC
    cO
    cop
    #
    cM
    ccurf
    co
    #
    yonval.y
    wph
    vc
    cC
    vc
    cv
    #
    @2
    coppc
    cfv
    #
    cop
    #
    @3
    chof
    cfv
    #
    ccurf
    co
    #
    @1
    ccat
    cyon
    cvv
    cyon
    vc
    ccat
    @6
    cmpt
    wceq
    wph
    vc
    df-yon
    a1i
    wph
    @2
    cC
    wceq
    #
    wa
    #
    @4
    @0
    @5
    cM
    ccurf
    @8
    @2
    cC
    @3
    cO
    wph
    @7
    simpr
    #
    @8
    @3
    cC
    coppc
    cfv
    cO
    @8
    @2
    cC
    coppc
    @9
    fveq2d
    yonval.o
    syl6eqr
    #
    opeq12d
    @8
    @5
    cO
    chof
    cfv
    cM
    @8
    @3
    cO
    chof
    @10
    fveq2d
    yonval.m
    syl6eqr
    oveq12d
    yonval.c
    wph
    @0
    cM
    ccurf
    ovexd
    fvmptd
    syl5eq
end
