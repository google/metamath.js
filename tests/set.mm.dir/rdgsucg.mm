include "crdg.mm"
include "cdm.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "wceq.mm"
include "wlim.mm"
include "wb.mm"
include "rdgdmlim.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "crn.mm"
include "cuni.mm"
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
include "limord.mm"
include "tz7.44-2.mm"
include "sylbi.mm"

theorem rdgsucg
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w


  assert |- ( B e. dom rec ( F , A ) -> ( rec ( F , A ) ` suc B ) = ( F ` ( rec ( F , A ) ` B ) ) )

  proof
    cB
    cF
    cA
    crdg
    #
    cdm
    #
    wcel
    #
    cB
    csuc
    #
    @1
    wcel
    #
    @3
    @0
    cfv
    cB
    @0
    cfv
    cF
    cfv
    wceq
    @1
    wlim
    #
    @2
    @4
    wb
    cA
    cF
    rdgdmlim
    #
    @1
    cB
    limsuc
    ax-mp
    vx
    vy
    cA
    cB
    @0
    vx
    cvv
    vx
    cv
    #
    c0
    wceq
    cA
    @7
    cdm
    #
    wlim
    @7
    crn
    cuni
    @8
    cuni
    @7
    cfv
    cF
    cfv
    cif
    cif
    cmpt
    #
    cF
    @1
    @9
    eqid
    cA
    vy
    cv
    #
    vx
    cF
    rdgvalg
    cA
    @10
    cF
    rdgseg
    @0
    wfun
    @0
    @1
    wfn
    cA
    cF
    rdgfun
    @0
    funfn
    mpbi
    @5
    @1
    word
    @6
    @1
    limord
    ax-mp
    tz7.44-2
    sylbi
end
