include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"
include "ralrimiva.mm"

theorem symgmov1
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  assume symgmov1.p: |- P = ( Base ` ( SymGrp ` N ) )

  disjoint N k
  disjoint N n
  disjoint k n
  disjoint P n
  disjoint Q k
  disjoint Q n
  assert |- ( Q e. P -> A. n e. N E. k e. N ( Q ` n ) = k )

  proof
    cQ
    cP
    wcel
    #
    vn
    cv
    #
    cQ
    cfv
    #
    vk
    cv
    #
    wceq
    #
    vk
    cN
    wrex
    #
    vn
    cN
    @0
    @1
    cN
    wcel
    wa
    @2
    cN
    wcel
    #
    @5
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    @1
    @7
    eqid
    symgmov1.p
    symgfv
    @6
    @3
    @2
    wceq
    #
    vk
    cN
    wrex
    @5
    vk
    @2
    cN
    risset
    @8
    @4
    vk
    cN
    @3
    @2
    eqcom
    rexbii
    bitri
    sylib
    ralrimiva
end
