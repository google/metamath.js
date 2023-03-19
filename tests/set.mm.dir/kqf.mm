include "ctop.mm"
include "ct0.mm"
include "ckq.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cuni.mm"
include "crab.mm"
include "cmpt.mm"
include "cqtop.mm"
include "co.mm"
include "ovex.mm"
include "df-kq.mm"
include "fnmpti.mm"
include "kqt0.mm"
include "biimpi.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem kqf
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cJ: class J
  let cX: class X


  assert |- KQ : Top --> Kol2

  proof
    ctop
    ct0
    ckq
    wf
    ckq
    ctop
    wfn
    vx
    cv
    #
    ckq
    cfv
    ct0
    wcel
    #
    vx
    ctop
    wral
    vj
    ctop
    vj
    cv
    #
    vx
    @2
    cuni
    @0
    vy
    cv
    wcel
    vy
    @2
    crab
    cmpt
    #
    cqtop
    co
    ckq
    @2
    @3
    cqtop
    ovex
    vx
    vy
    vj
    df-kq
    fnmpti
    @1
    vx
    ctop
    @0
    ctop
    wcel
    @1
    @0
    kqt0
    biimpi
    rgen
    vx
    ctop
    ct0
    ckq
    ffnfv
    mpbir2an
end
