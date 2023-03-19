include "wcel.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "wsbc.mm"
include "csb.mm"
include "wfun.mm"
include "sbcan.mm"
include "sbcrel.mm"
include "sbcal.mm"
include "sbcex2.mm"
include "sbcimg.mm"
include "sbcbr123.mm"
include "csbconstg.mm"
include "breq12d.mm"
include "syl5bb.mm"
include "sbcg.mm"
include "imbi12d.mm"
include "bitrd.mm"
include "albidv.mm"
include "exbidv.mm"
include "anbi12d.mm"
include "dffun3.mm"
include "sbcbii.mm"
include "3bitr4g.mm"

theorem sbcfung
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> ( [. A / x ]. Fun F <-> Fun [_ A / x ]_ F ) )

  proof
    cA
    cV
    wcel
    #
    cF
    wrel
    #
    vw
    cv
    #
    vz
    cv
    #
    cF
    wbr
    #
    vz
    vy
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vw
    wal
    #
    wa
    #
    vx
    cA
    wsbc
    #
    vx
    cA
    cF
    csb
    #
    wrel
    #
    @2
    @3
    @12
    wbr
    #
    @5
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vw
    wal
    #
    wa
    #
    cF
    wfun
    #
    vx
    cA
    wsbc
    @12
    wfun
    @11
    @1
    vx
    cA
    wsbc
    #
    @9
    vx
    cA
    wsbc
    #
    wa
    @0
    @19
    @1
    @9
    vx
    cA
    sbcan
    @0
    @21
    @13
    @22
    @18
    vx
    cA
    cF
    cV
    sbcrel
    @22
    @8
    vx
    cA
    wsbc
    #
    vw
    wal
    @0
    @18
    @8
    vw
    vx
    cA
    sbcal
    @0
    @23
    @17
    vw
    @23
    @7
    vx
    cA
    wsbc
    #
    vy
    wex
    @0
    @17
    @7
    vy
    vx
    cA
    sbcex2
    @0
    @24
    @16
    vy
    @24
    @6
    vx
    cA
    wsbc
    #
    vz
    wal
    @0
    @16
    @6
    vz
    vx
    cA
    sbcal
    @0
    @25
    @15
    vz
    @0
    @25
    @4
    vx
    cA
    wsbc
    #
    @5
    vx
    cA
    wsbc
    #
    wi
    @15
    @4
    @5
    vx
    cA
    cV
    sbcimg
    @0
    @26
    @14
    @27
    @5
    @26
    vx
    cA
    @2
    csb
    #
    vx
    cA
    @3
    csb
    #
    @12
    wbr
    @0
    @14
    vx
    cA
    @2
    @3
    cF
    sbcbr123
    @0
    @28
    @2
    @29
    @3
    @12
    vx
    cA
    @2
    cV
    csbconstg
    vx
    cA
    @3
    cV
    csbconstg
    breq12d
    syl5bb
    @5
    vx
    cA
    cV
    sbcg
    imbi12d
    bitrd
    albidv
    syl5bb
    exbidv
    syl5bb
    albidv
    syl5bb
    anbi12d
    syl5bb
    @20
    @10
    vx
    cA
    vw
    vz
    vy
    cF
    dffun3
    sbcbii
    vw
    vz
    vy
    @12
    dffun3
    3bitr4g
end
