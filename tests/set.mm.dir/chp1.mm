include "c1.mm"
include "cchp.mm"
include "cfv.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "1re.mm"
include "chpval.mm"
include "ax-mp.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "vma1.mm"
include "syl6eq.mm"
include "cz.mm"
include "1z.mm"
include "flid.mm"
include "oveq2i.mm"
include "eleq2s.mm"
include "sumeq2i.mm"
include "cuz.mm"
include "wss.mm"
include "cfn.mm"
include "wo.mm"
include "fzfi.mm"
include "olci.mm"
include "sumz.mm"
include "3eqtri.mm"

theorem chp1
  let vk: setvar k
  let vp: setvar p
  let vx: setvar x


  assert |- ( psi ` 1 ) = 0

  proof
    c1
    cchp
    cfv
    #
    c1
    c1
    cfl
    cfv
    #
    cfz
    co
    #
    vx
    cv
    #
    cvma
    cfv
    #
    vx
    csu
    #
    @2
    cc0
    vx
    csu
    #
    cc0
    c1
    cr
    wcel
    @0
    @5
    wceq
    1re
    c1
    vx
    chpval
    ax-mp
    @2
    @4
    cc0
    vx
    @4
    cc0
    wceq
    @3
    c1
    c1
    cfz
    co
    #
    @2
    @3
    @7
    wcel
    #
    @4
    c1
    cvma
    cfv
    cc0
    @8
    @3
    c1
    cvma
    @3
    c1
    elfz1eq
    fveq2d
    vma1
    syl6eq
    @1
    c1
    c1
    cfz
    c1
    cz
    wcel
    @1
    c1
    wceq
    1z
    c1
    flid
    ax-mp
    oveq2i
    eleq2s
    sumeq2i
    @2
    c1
    cuz
    cfv
    wss
    #
    @2
    cfn
    wcel
    #
    wo
    @6
    cc0
    wceq
    @10
    @9
    c1
    @1
    fzfi
    olci
    @2
    vx
    c1
    sumz
    ax-mp
    3eqtri
end
