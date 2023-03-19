include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cpw.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cmap.mm"
include "crab.mm"
include "df-cncf.mm"
include "elmpt2cl1.mm"
include "elpwid.mm"

theorem cncfrss
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cR: class R


  assert |- ( F e. ( A -cn-> B ) -> A C_ CC )

  proof
    cF
    cA
    cB
    ccncf
    co
    wcel
    cA
    cc
    va
    vb
    cc
    cpw
    #
    @0
    vx
    cv
    #
    vw
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    @1
    vf
    cv
    #
    cfv
    @2
    @3
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    wi
    vw
    va
    cv
    #
    wral
    vz
    crp
    wrex
    vy
    crp
    wral
    vx
    @4
    wral
    vf
    vb
    cv
    @4
    cmap
    co
    crab
    cA
    cB
    ccncf
    cF
    vx
    vw
    vy
    vf
    va
    vb
    vz
    df-cncf
    elmpt2cl1
    elpwid
end
