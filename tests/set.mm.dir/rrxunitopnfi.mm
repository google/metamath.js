include "cfn.mm"
include "wcel.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "cuni.mm"
include "eqidd.mm"
include "ctopon.mm"
include "wceq.mm"
include "eqid.mm"
include "rrxtoponfi.mm"
include "toponuni.mm"
include "syl.mm"
include "eqtr2d.mm"

theorem rrxunitopnfi
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( X e. Fin -> U. ( TopOpen ` ( RR^ ` X ) ) = ( RR ^m X ) )

  proof
    cX
    cfn
    wcel
    #
    cr
    cX
    cmap
    co
    #
    @1
    cX
    crrx
    cfv
    ctopn
    cfv
    #
    cuni
    #
    @0
    @1
    eqidd
    @0
    @2
    @1
    ctopon
    cfv
    wcel
    @1
    @3
    wceq
    cX
    @2
    @2
    eqid
    rrxtoponfi
    @1
    @2
    toponuni
    syl
    eqtr2d
end
