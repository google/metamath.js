include "cv.mm"
include "wfun.mm"
include "cab.mm"
include "cvv.mm"
include "ccnv.mm"
include "wbr.mm"
include "cima.mm"
include "corvc.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-orvc.mm"
include "a1i.mm"
include "wa.mm"
include "simpl.mm"
include "cnveqd.mm"
include "simpr.mm"
include "breq2d.mm"
include "abbidv.mm"
include "imaeq12d.mm"
include "adantl.mm"
include "wcel.mm"
include "wb.mm"
include "funeq.mm"
include "elabg.mm"
include "syl.mm"
include "mpbird.mm"
include "elex.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "3syl.mm"
include "ovmpt2d.mm"

theorem orvcval
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume orvcval.1: |- ( ph -> Fun X )
  assume orvcval.2: |- ( ph -> X e. V )
  assume orvcval.3: |- ( ph -> A e. W )

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint x y
  disjoint A x
  disjoint R a
  disjoint R x
  disjoint X a
  disjoint X x
  disjoint a ph
  disjoint ph x
  assert |- ( ph -> ( X oRVC R A ) = ( `' X " { y | y R A } ) )

  proof
    wph
    vx
    va
    cX
    cA
    vx
    cv
    #
    wfun
    #
    vx
    cab
    #
    cvv
    @0
    ccnv
    #
    vy
    cv
    #
    va
    cv
    #
    cR
    wbr
    #
    vy
    cab
    #
    cima
    #
    cX
    ccnv
    #
    @4
    cA
    cR
    wbr
    #
    vy
    cab
    #
    cima
    #
    cR
    corvc
    #
    cvv
    @13
    vx
    va
    @2
    cvv
    @8
    cmpt2
    wceq
    wph
    vx
    vy
    cR
    va
    df-orvc
    a1i
    @0
    cX
    wceq
    #
    @5
    cA
    wceq
    #
    wa
    #
    @8
    @12
    wceq
    wph
    @16
    @3
    @9
    @7
    @11
    @16
    @0
    cX
    @14
    @15
    simpl
    cnveqd
    @16
    @6
    @10
    vy
    @16
    @5
    cA
    @4
    cR
    @14
    @15
    simpr
    breq2d
    abbidv
    imaeq12d
    adantl
    wph
    cX
    @2
    wcel
    #
    cX
    wfun
    #
    orvcval.1
    wph
    cX
    cV
    wcel
    #
    @17
    @18
    wb
    orvcval.2
    @1
    @18
    vx
    cX
    cV
    @0
    cX
    funeq
    elabg
    syl
    mpbird
    wph
    cA
    cW
    wcel
    cA
    cvv
    wcel
    orvcval.3
    cA
    cW
    elex
    syl
    wph
    @19
    @9
    cvv
    wcel
    @12
    cvv
    wcel
    orvcval.2
    cX
    cV
    cnvexg
    @9
    @11
    cvv
    imaexg
    3syl
    ovmpt2d
end
