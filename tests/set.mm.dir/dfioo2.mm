include "cioo.mm"
include "cxr.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "crab.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnov.mm"
include "mpbi.mm"
include "iooval2.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"

theorem dfioo2
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint w x
  disjoint w y
  disjoint x y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  assert |- (,) = ( x e. RR* , y e. RR* |-> { w e. RR | ( x < w /\ w < y ) } )

  proof
    cioo
    vx
    vy
    cxr
    cxr
    vx
    cv
    #
    vy
    cv
    #
    cioo
    co
    #
    cmpt2
    #
    vx
    vy
    cxr
    cxr
    @0
    vw
    cv
    #
    clt
    wbr
    @4
    @1
    clt
    wbr
    wa
    vw
    cr
    crab
    #
    cmpt2
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    cioo
    @3
    wceq
    @6
    cr
    cpw
    #
    cioo
    wf
    @7
    ioof
    @6
    @8
    cioo
    ffn
    ax-mp
    vx
    vy
    cxr
    cxr
    cioo
    fnov
    mpbi
    vx
    vy
    cxr
    cxr
    @2
    @5
    vw
    @0
    @1
    iooval2
    mpt2eq3ia
    eqtri
end
