include "cv.mm"
include "cfv.mm"
include "cima.mm"
include "cdif.mm"
include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cop.mm"
include "vex.mm"
include "elrn2.mm"
include "cdm.mm"
include "opeldm.mm"
include "wfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleq.mm"
include "ancri.mm"
include "wb.mm"
include "fnopfvb.mm"
include "mpan.mm"
include "pm5.32i.mm"
include "sylibr.mm"
include "eximi.mm"
include "sylbi.mm"
include "nfra1.mm"
include "nfv.mm"
include "wi.mm"
include "rsp.mm"
include "eldifi.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "imim2i.mm"
include "impd.mm"
include "syl.mm"
include "exlimd.mm"
include "syl5.mm"
include "ssrdv.mm"

theorem tz7.48-1
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume tz7.48.1: |- F Fn On

  disjoint F x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint F y
  disjoint F z
  disjoint F w
  assert |- ( A. x e. On ( F ` x ) e. ( A \ ( F " x ) ) -> ran F C_ A )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    cA
    cF
    @0
    cima
    #
    cdif
    wcel
    #
    vx
    con0
    wral
    #
    vy
    cF
    crn
    #
    cA
    vy
    cv
    #
    @5
    wcel
    #
    @0
    con0
    wcel
    #
    @1
    @6
    wceq
    #
    wa
    #
    vx
    wex
    #
    @4
    @6
    cA
    wcel
    #
    @7
    @0
    @6
    cop
    cF
    wcel
    #
    vx
    wex
    @11
    vx
    @6
    cF
    vy
    vex
    #
    elrn2
    @13
    @10
    vx
    @13
    @8
    @13
    wa
    @10
    @13
    @8
    @13
    @0
    cF
    cdm
    #
    con0
    @0
    @6
    cF
    vx
    vex
    @14
    opeldm
    cF
    con0
    wfn
    #
    @15
    con0
    wceq
    tz7.48.1
    con0
    cF
    fndm
    ax-mp
    syl6eleq
    ancri
    @8
    @9
    @13
    @16
    @8
    @9
    @13
    wb
    tz7.48.1
    con0
    @0
    @6
    cF
    fnopfvb
    mpan
    pm5.32i
    sylibr
    eximi
    sylbi
    @4
    @10
    @12
    vx
    @3
    vx
    con0
    nfra1
    @12
    vx
    nfv
    @4
    @8
    @3
    wi
    #
    @10
    @12
    wi
    @3
    vx
    con0
    rsp
    @17
    @8
    @9
    @12
    @3
    @9
    @12
    wi
    @8
    @3
    @1
    cA
    wcel
    @9
    @12
    @1
    cA
    @2
    eldifi
    @1
    @6
    cA
    eleq1
    syl5ibcom
    imim2i
    impd
    syl
    exlimd
    syl5
    ssrdv
end
