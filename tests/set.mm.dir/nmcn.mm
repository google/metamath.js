include "cngp.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "cds.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "eqid.mm"
include "nmfval.mm"
include "ngpms.mm"
include "ctps.mm"
include "ctopon.mm"
include "ngptps.mm"
include "istps.mm"
include "sylib.mm"
include "cnmptid.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "cnmptc.mm"
include "cnmpt1ds.mm"
include "syl5eqel.mm"

theorem nmcn
  let cG: class G
  let cJ: class J
  let cK: class K
  let cN: class N
  let vx: setvar x
  assume nmcn.n: |- N = ( norm ` G )
  assume nmcn.j: |- J = ( TopOpen ` G )
  assume nmcn.k: |- K = ( topGen ` ran (,) )


  assert |- ( G e. NrmGrp -> N e. ( J Cn K ) )

  proof
    cG
    cngp
    wcel
    #
    cN
    vx
    cG
    cbs
    cfv
    #
    vx
    cv
    #
    cG
    c0g
    cfv
    #
    cG
    cds
    cfv
    #
    co
    cmpt
    cJ
    cK
    ccn
    co
    vx
    @4
    cN
    cG
    @1
    @3
    nmcn.n
    @1
    eqid
    #
    @3
    eqid
    #
    @4
    eqid
    #
    nmfval
    @0
    vx
    @2
    @3
    @4
    cK
    cG
    cJ
    cJ
    @1
    @7
    nmcn.j
    nmcn.k
    cG
    ngpms
    @0
    cG
    ctps
    wcel
    cJ
    @1
    ctopon
    cfv
    wcel
    cG
    ngptps
    @1
    cJ
    cG
    @5
    nmcn.j
    istps
    sylib
    #
    @0
    vx
    cJ
    @1
    @8
    cnmptid
    @0
    vx
    @3
    cJ
    cJ
    @1
    @1
    @8
    @8
    @0
    cG
    cgrp
    wcel
    @3
    @1
    wcel
    cG
    ngpgrp
    @1
    cG
    @3
    @5
    @6
    grpidcl
    syl
    cnmptc
    cnmpt1ds
    syl5eqel
end
