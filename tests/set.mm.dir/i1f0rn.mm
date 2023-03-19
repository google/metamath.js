include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "crn.mm"
include "cpnf.mm"
include "cr.mm"
include "pnfnre.mm"
include "neli.mm"
include "wn.mm"
include "wa.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "wceq.mm"
include "rembl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ovolre.mm"
include "eqtri.mm"
include "ccnv.mm"
include "cima.mm"
include "cnvimarndm.mm"
include "wf.mm"
include "i1ff.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "i1fima2.mm"
include "eqeltrrd.mm"
include "syl5eqelr.mm"
include "ex.mm"
include "mt3i.mm"

theorem i1f0rn
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( F e. dom S.1 -> 0 e. ran F )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cc0
    cF
    crn
    #
    wcel
    #
    cpnf
    cr
    wcel
    #
    cpnf
    cr
    pnfnre
    neli
    @0
    @2
    wn
    #
    @3
    @0
    @4
    wa
    #
    cpnf
    cr
    cvol
    cfv
    #
    cr
    @6
    cr
    covol
    cfv
    #
    cpnf
    cr
    cvol
    cdm
    wcel
    @6
    @7
    wceq
    rembl
    cr
    mblvol
    ax-mp
    ovolre
    eqtri
    @5
    cF
    ccnv
    @1
    cima
    #
    cvol
    cfv
    @6
    cr
    @5
    @8
    cr
    cvol
    @5
    @8
    cF
    cdm
    #
    cr
    cF
    cnvimarndm
    @0
    @9
    cr
    wceq
    #
    @4
    @0
    cr
    cr
    cF
    wf
    @10
    cF
    i1ff
    cr
    cr
    cF
    fdm
    syl
    adantr
    syl5eq
    fveq2d
    @1
    cF
    i1fima2
    eqeltrrd
    syl5eqelr
    ex
    mt3i
end
