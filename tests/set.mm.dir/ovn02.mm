include "c0.mm"
include "covoln.mm"
include "cfv.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cv.mm"
include "cmpt.mm"
include "csn.mm"
include "cc0.mm"
include "wtru.mm"
include "wceq.mm"
include "tru.mm"
include "cpnf.mm"
include "cicc.mm"
include "cfn.mm"
include "wcel.mm"
include "0fin.mm"
include "a1i.mm"
include "ovnf.mm"
include "feqmptd.mm"
include "ax-mp.mm"
include "cvv.mm"
include "reex.mm"
include "mapdm0.mm"
include "pweqi.mm"
include "mpteq1.mm"
include "elpwi.mm"
include "eqcomi.mm"
include "sseqtrd.mm"
include "ovn0val.mm"
include "mpteq2ia.mm"
include "3eqtri.mm"

theorem ovn02
  let vx: setvar x
  let vk: setvar k


  assert |- ( voln* ` (/) ) = ( x e. ~P { (/) } |-> 0 )

  proof
    c0
    covoln
    cfv
    #
    vx
    cr
    c0
    cmap
    co
    #
    cpw
    #
    vx
    cv
    #
    @0
    cfv
    #
    cmpt
    #
    vx
    c0
    csn
    #
    cpw
    #
    @4
    cmpt
    #
    vx
    @7
    cc0
    cmpt
    wtru
    @0
    @5
    wceq
    tru
    wtru
    vx
    @2
    cc0
    cpnf
    cicc
    co
    @0
    wtru
    c0
    c0
    cfn
    wcel
    wtru
    0fin
    a1i
    ovnf
    feqmptd
    ax-mp
    @2
    @7
    wceq
    @5
    @8
    wceq
    @1
    @6
    cr
    cvv
    wcel
    @1
    @6
    wceq
    reex
    cr
    cvv
    mapdm0
    ax-mp
    #
    pweqi
    vx
    @2
    @7
    @4
    mpteq1
    ax-mp
    vx
    @7
    @4
    cc0
    @3
    @7
    wcel
    #
    @3
    @10
    @3
    @6
    @1
    @3
    @6
    elpwi
    @6
    @1
    wceq
    @10
    @1
    @6
    @9
    eqcomi
    a1i
    sseqtrd
    ovn0val
    mpteq2ia
    3eqtri
end
