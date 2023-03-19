include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "estrchomfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem estrchomfn
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume estrchomfn.c: |- C = ( ExtStrCat ` U )
  assume estrchomfn.u: |- ( ph -> U e. V )
  assume estrchomfn.h: |- H = ( Hom ` C )


  assert |- ( ph -> H Fn ( U X. U ) )

  proof
    wph
    cH
    cU
    cU
    cxp
    #
    wfn
    vx
    vy
    cU
    cU
    vy
    cv
    cbs
    cfv
    #
    vx
    cv
    cbs
    cfv
    #
    cmap
    co
    #
    cmpt2
    #
    @0
    wfn
    vx
    vy
    cU
    cU
    @3
    @4
    @4
    eqid
    @1
    @2
    cmap
    ovex
    fnmpt2i
    wph
    @0
    cH
    @4
    wph
    vx
    vy
    cC
    cU
    cH
    cV
    estrchomfn.c
    estrchomfn.u
    estrchomfn.h
    estrchomfval
    fneq1d
    mpbiri
end
