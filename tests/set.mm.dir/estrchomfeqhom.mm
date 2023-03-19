include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "wfn.mm"
include "chomf.mm"
include "wceq.mm"
include "estrchomfn.mm"
include "estrcbas.mm"
include "eqcomd.mm"
include "sqxpeqd.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "eqid.mm"
include "fnhomeqhomf.mm"
include "syl.mm"

theorem estrchomfeqhom
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


  assert |- ( ph -> ( Homf ` C ) = H )

  proof
    wph
    cH
    cC
    cbs
    cfv
    #
    @0
    cxp
    #
    wfn
    #
    cC
    chomf
    cfv
    #
    cH
    wceq
    wph
    @2
    cH
    cU
    cU
    cxp
    #
    wfn
    wph
    cC
    cU
    cH
    cV
    estrchomfn.c
    estrchomfn.u
    estrchomfn.h
    estrchomfn
    wph
    @1
    @4
    cH
    wph
    @0
    cU
    wph
    cU
    @0
    wph
    cC
    cU
    cV
    estrchomfn.c
    estrchomfn.u
    estrcbas
    eqcomd
    sqxpeqd
    fneq2d
    mpbird
    @0
    cC
    @3
    cH
    @3
    eqid
    @0
    eqid
    estrchomfn.h
    fnhomeqhomf
    syl
end
