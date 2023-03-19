include "cdiag.mm"
include "co.mm"
include "cop.mm"
include "c1stf.mm"
include "ccurf.mm"
include "ccat.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-diag.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem diagval
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cL: class L
  let vc: setvar c
  let vd: setvar d
  assume diagval.l: |- L = ( C DiagFunc D )
  assume diagval.c: |- ( ph -> C e. Cat )
  assume diagval.d: |- ( ph -> D e. Cat )


  assert |- ( ph -> L = ( <. C , D >. curryF ( C 1stF D ) ) )

  proof
    wph
    cL
    cC
    cD
    cdiag
    co
    cC
    cD
    cop
    #
    cC
    cD
    c1stf
    co
    #
    ccurf
    co
    #
    diagval.l
    wph
    vc
    vd
    cC
    cD
    ccat
    ccat
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    @3
    @4
    c1stf
    co
    #
    ccurf
    co
    #
    @2
    cdiag
    cvv
    cdiag
    vc
    vd
    ccat
    ccat
    @7
    cmpt2
    wceq
    wph
    vc
    vd
    df-diag
    a1i
    wph
    @3
    cC
    wceq
    #
    @4
    cD
    wceq
    #
    wa
    wa
    #
    @5
    @0
    @6
    @1
    ccurf
    @10
    @3
    cC
    @4
    cD
    wph
    @8
    @9
    simprl
    #
    wph
    @8
    @9
    simprr
    #
    opeq12d
    @10
    @3
    cC
    @4
    cD
    c1stf
    @11
    @12
    oveq12d
    oveq12d
    diagval.c
    diagval.d
    wph
    @0
    @1
    ccurf
    ovexd
    ovmpt2d
    syl5eq
end
