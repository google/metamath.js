include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "ccnfld.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "crefld.mm"
include "cmul.mm"
include "csubg.mm"
include "wceq.mm"
include "c1.mm"
include "cv.mm"
include "recn.mm"
include "readdcl.mm"
include "renegcl.mm"
include "1re.mm"
include "cnsubglem.mm"
include "eqid.mm"
include "df-refld.mm"
include "subgmulg.mm"
include "mp3an1.mm"
include "cc.mm"
include "simpr.mm"
include "recnd.mm"
include "cnfldmulg.mm"
include "syldan.mm"
include "eqtr3d.mm"

theorem remulg
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( N e. ZZ /\ A e. RR ) -> ( N ( .g ` RRfld ) A ) = ( N x. A ) )

  proof
    cN
    cz
    wcel
    #
    cA
    cr
    wcel
    #
    wa
    #
    cN
    cA
    ccnfld
    cmg
    cfv
    #
    co
    #
    cN
    cA
    crefld
    cmg
    cfv
    #
    co
    #
    cN
    cA
    cmul
    co
    #
    cr
    ccnfld
    csubg
    cfv
    wcel
    @0
    @1
    @4
    @6
    wceq
    vx
    vy
    cr
    c1
    vx
    cv
    #
    recn
    @8
    vy
    cv
    readdcl
    @8
    renegcl
    1re
    cnsubglem
    cr
    @5
    @3
    ccnfld
    crefld
    cN
    cA
    @3
    eqid
    df-refld
    @5
    eqid
    subgmulg
    mp3an1
    @0
    @1
    cA
    cc
    wcel
    @4
    @7
    wceq
    @2
    cA
    @0
    @1
    simpr
    recnd
    cN
    cA
    cnfldmulg
    syldan
    eqtr3d
end
