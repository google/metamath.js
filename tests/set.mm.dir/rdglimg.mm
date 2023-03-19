include "crdg.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "rdgvalg.mm"
include "rdgseg.mm"
include "wfun.mm"
include "wfn.mm"
include "rdgfun.mm"
include "funfn.mm"
include "mpbi.mm"
include "word.mm"
include "rdgdmlim.mm"
include "limord.mm"
include "ax-mp.mm"
include "tz7.44-3.mm"

theorem rdglimg
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( B e. dom rec ( F , A ) /\ Lim B ) -> ( rec ( F , A ) ` B ) = U. ( rec ( F , A ) " B ) )

  proof
    vx
    vy
    cA
    cB
    cF
    cA
    crdg
    #
    vx
    cvv
    vx
    cv
    #
    c0
    wceq
    cA
    @1
    cdm
    #
    wlim
    @1
    crn
    cuni
    @2
    cuni
    @1
    cfv
    cF
    cfv
    cif
    cif
    cmpt
    #
    cF
    @0
    cdm
    #
    @3
    eqid
    cA
    vy
    cv
    #
    vx
    cF
    rdgvalg
    cA
    @5
    cF
    rdgseg
    @0
    wfun
    @0
    @4
    wfn
    cA
    cF
    rdgfun
    @0
    funfn
    mpbi
    @4
    wlim
    @4
    word
    cA
    cF
    rdgdmlim
    @4
    limord
    ax-mp
    tz7.44-3
end
