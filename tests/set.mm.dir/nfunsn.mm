include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wn.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "weu.mm"
include "eumo.mm"
include "wcel.mm"
include "vex.mm"
include "brres.mm"
include "wb.mm"
include "velsn.mm"
include "breq1.mm"
include "sylbi.mm"
include "biimpac.mm"
include "moimi.mm"
include "syl.mm"
include "tz6.12-2.mm"
include "nsyl4.mm"
include "alrimiv.mm"
include "relres.mm"
include "jctil.mm"
include "dffun6.mm"
include "sylibr.mm"
include "con1i.mm"

theorem nfunsn
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. Fun ( F |` { A } ) -> ( F ` A ) = (/) )

  proof
    cA
    cF
    cfv
    c0
    wceq
    #
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    @0
    wn
    #
    @2
    wrel
    #
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
    #
    wa
    @3
    @4
    @10
    @5
    @4
    @9
    vx
    cA
    @7
    cF
    wbr
    #
    vy
    weu
    #
    @9
    @0
    @12
    @11
    vy
    wmo
    @9
    @11
    vy
    eumo
    @8
    @11
    vy
    @8
    @6
    @7
    cF
    wbr
    #
    @6
    @1
    wcel
    #
    wa
    @11
    @6
    @7
    cF
    @1
    vy
    vex
    brres
    @14
    @13
    @11
    @14
    @6
    cA
    wceq
    @13
    @11
    wb
    vx
    cA
    velsn
    @6
    cA
    @7
    cF
    breq1
    sylbi
    biimpac
    sylbi
    moimi
    syl
    vy
    cA
    cF
    tz6.12-2
    nsyl4
    alrimiv
    cF
    @1
    relres
    jctil
    vx
    vy
    @2
    dffun6
    sylibr
    con1i
end
