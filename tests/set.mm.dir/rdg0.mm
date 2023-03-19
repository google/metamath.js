include "c0.mm"
include "crdg.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "com.mm"
include "wlim.mm"
include "wss.mm"
include "rdgdmlim.mm"
include "limomss.mm"
include "ax-mp.mm"
include "peano1.mm"
include "sselii.mm"
include "cvv.mm"
include "cv.mm"
include "crn.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "rdgvalg.mm"
include "tz7.44-1.mm"

theorem rdg0
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  assume rdg.1: |- A e. _V


  assert |- ( rec ( F , A ) ` (/) ) = A

  proof
    c0
    cF
    cA
    crdg
    #
    cdm
    #
    wcel
    c0
    @0
    cfv
    cA
    wceq
    com
    @1
    c0
    @1
    wlim
    com
    @1
    wss
    cA
    cF
    rdgdmlim
    @1
    limomss
    ax-mp
    peano1
    sselii
    vx
    vy
    cA
    @0
    vx
    cvv
    vx
    cv
    #
    c0
    wceq
    cA
    @2
    cdm
    #
    wlim
    @2
    crn
    cuni
    @3
    cuni
    @2
    cfv
    cF
    cfv
    cif
    cif
    cmpt
    #
    cF
    @1
    @4
    eqid
    cA
    vy
    cv
    vx
    cF
    rdgvalg
    rdg.1
    tz7.44-1
    ax-mp
end
