include "cpgp.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cprime.mm"
include "chash.mm"
include "cfv.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "simpl.mm"
include "cgrp.mm"
include "wb.mm"
include "pgpgrp.mm"
include "pgpfi2.mm"
include "sylan.mm"
include "mpbid.mm"
include "simprd.mm"

theorem pgphash
  let cP: class P
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  assume pgpfi.1: |- X = ( Base ` G )


  assert |- ( ( P pGrp G /\ X e. Fin ) -> ( # ` X ) = ( P ^ ( P pCnt ( # ` X ) ) ) )

  proof
    cP
    cG
    cpgp
    wbr
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cP
    cprime
    wcel
    #
    cX
    chash
    cfv
    #
    cP
    cP
    @4
    cpc
    co
    cexp
    co
    wceq
    #
    @2
    @0
    @3
    @5
    wa
    #
    @0
    @1
    simpl
    @0
    cG
    cgrp
    wcel
    @1
    @0
    @6
    wb
    cP
    cG
    pgpgrp
    cP
    cG
    cX
    pgpfi.1
    pgpfi2
    sylan
    mpbid
    simprd
end
