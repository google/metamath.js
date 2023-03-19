include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "relcnv.mm"
include "wceq.mm"
include "moeq.mm"
include "wcel.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "bitri.mm"
include "elsni.mm"
include "opth1.mm"
include "syl.mm"
include "sylbi.mm"
include "moimi.mm"
include "ax-mp.mm"
include "ax-gen.mm"
include "dffun6.mm"
include "mpbir2an.mm"

theorem funcnvsn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- Fun `' { <. A , B >. }

  proof
    cA
    cB
    cop
    #
    csn
    #
    ccnv
    #
    wfun
    @2
    wrel
    vx
    cv
    #
    vy
    cv
    #
    @2
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    @1
    relcnv
    @6
    vx
    @4
    cA
    wceq
    #
    vy
    wmo
    @6
    vy
    cA
    moeq
    @5
    @7
    vy
    @5
    @4
    @3
    cop
    #
    @1
    wcel
    #
    @7
    @5
    @4
    @3
    @1
    wbr
    @9
    @3
    @4
    @1
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    @4
    @3
    @1
    df-br
    bitri
    @9
    @8
    @0
    wceq
    @7
    @8
    @0
    elsni
    @4
    @3
    cA
    cB
    @11
    @10
    opth1
    syl
    sylbi
    moimi
    ax-mp
    ax-gen
    vx
    vy
    @2
    dffun6
    mpbir2an
end
