include "wcel.mm"
include "ccat.mm"
include "ccid.mm"
include "cfv.mm"
include "cid.mm"
include "cv.mm"
include "cbs.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "estrccatid.mm"
include "simpld.mm"

theorem estrccat
  let cC: class C
  let cU: class U
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume estrccat.c: |- C = ( ExtStrCat ` U )


  assert |- ( U e. V -> C e. Cat )

  proof
    cU
    cV
    wcel
    cC
    ccat
    wcel
    cC
    ccid
    cfv
    vx
    cU
    cid
    vx
    cv
    cbs
    cfv
    cres
    cmpt
    wceq
    vx
    cC
    cU
    cV
    estrccat.c
    estrccatid
    simpld
end
