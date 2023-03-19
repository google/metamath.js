include "wcel.mm"
include "ccat.mm"
include "ccid.mm"
include "cfv.mm"
include "cbs.mm"
include "cid.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqid.mm"
include "rngccatidALTV.mm"
include "simpld.mm"

theorem rngccatALTV
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
  let cB: class B
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  assume rngccatALTV.c: |- C = ( RngCatALTV ` U )


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
    cC
    cbs
    cfv
    #
    cid
    vx
    cv
    cbs
    cfv
    cres
    cmpt
    wceq
    vx
    @0
    cC
    cU
    cV
    rngccatALTV.c
    @0
    eqid
    rngccatidALTV
    simpld
end
