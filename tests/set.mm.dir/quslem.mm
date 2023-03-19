include "crn.mm"
include "wfo.mm"
include "cqs.mm"
include "wfn.mm"
include "cv.mm"
include "cec.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "ecexg.mm"
include "syl.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "dffn4.mm"
include "sylib.mm"
include "wceq.mm"
include "wb.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "df-qs.mm"
include "eqtr4i.mm"
include "foeq3.mm"
include "ax-mp.mm"

theorem quslem
  let wph: wff ph
  let vx: setvar x
  let c.sm: class .~
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let ve: setvar e
  let vr: setvar r
  let vy: setvar y
  assume qusval.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusval.v: |- ( ph -> V = ( Base ` R ) )
  assume qusval.f: |- F = ( x e. V |-> [ x ] .~ )
  assume qusval.e: |- ( ph -> .~ e. W )
  assume qusval.r: |- ( ph -> R e. Z )

  disjoint .~ x
  disjoint ph x
  disjoint R x
  disjoint V x
  disjoint e r
  disjoint e x
  disjoint e y
  disjoint .~ e
  disjoint r x
  disjoint r y
  disjoint .~ r
  disjoint x y
  disjoint .~ y
  disjoint F e
  disjoint F r
  disjoint e ph
  disjoint ph r
  disjoint R e
  disjoint R r
  disjoint V y
  assert |- ( ph -> F : V -onto-> ( V /. .~ ) )

  proof
    wph
    cV
    cF
    crn
    #
    cF
    wfo
    #
    cV
    cV
    c.sm
    cqs
    #
    cF
    wfo
    #
    wph
    cF
    cV
    wfn
    #
    @1
    wph
    vx
    cv
    #
    c.sm
    cec
    #
    cvv
    wcel
    #
    vx
    cV
    wral
    @4
    wph
    @7
    vx
    cV
    wph
    c.sm
    cW
    wcel
    @7
    qusval.e
    @5
    cW
    c.sm
    ecexg
    syl
    ralrimivw
    vx
    cV
    @6
    cF
    cvv
    qusval.f
    fnmpt
    syl
    cV
    cF
    dffn4
    sylib
    @0
    @2
    wceq
    @1
    @3
    wb
    @0
    vy
    cv
    @6
    wceq
    vx
    cV
    wrex
    vy
    cab
    @2
    vx
    vy
    cV
    @6
    cF
    qusval.f
    rnmpt
    vx
    vy
    cV
    c.sm
    df-qs
    eqtr4i
    @0
    @2
    cV
    cF
    foeq3
    ax-mp
    sylib
end
