include "wcel.mm"
include "crdg.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "rdg0g.mm"
include "eleq1a.mm"
include "mpd.mm"
include "cv.mm"
include "com.mm"
include "csuc.mm"
include "wi.mm"
include "con0.mm"
include "nnon.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "vtoclga.mm"
include "rdgsuc.mm"
include "syl5ibr.mm"
include "syl.mm"
include "a1d.mm"
include "findfvcl.mm"

theorem findreccl
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cP: class P
  let cG: class G
  let vy: setvar y
  assume findreccl.1: |- ( z e. P -> ( G ` z ) e. P )

  disjoint G z
  disjoint A z
  disjoint P z
  disjoint y z
  disjoint G y
  disjoint A y
  disjoint P y
  assert |- ( C e. _om -> ( A e. P -> ( rec ( G , A ) ` C ) e. P ) )

  proof
    cA
    cP
    wcel
    #
    vy
    cC
    cP
    cG
    cA
    crdg
    #
    @0
    c0
    @1
    cfv
    #
    cA
    wceq
    @2
    cP
    wcel
    cA
    cP
    cG
    rdg0g
    cA
    cP
    @2
    eleq1a
    mpd
    vy
    cv
    #
    com
    wcel
    #
    @3
    @1
    cfv
    #
    cP
    wcel
    #
    @3
    csuc
    @1
    cfv
    #
    cP
    wcel
    #
    wi
    #
    @0
    @4
    @3
    con0
    wcel
    #
    @9
    @3
    nnon
    @6
    @8
    @10
    @5
    cG
    cfv
    #
    cP
    wcel
    #
    vz
    cv
    #
    cG
    cfv
    #
    cP
    wcel
    @12
    vz
    @5
    cP
    @13
    @5
    wceq
    @14
    @11
    cP
    @13
    @5
    cG
    fveq2
    eleq1d
    findreccl.1
    vtoclga
    @10
    @7
    @11
    cP
    cA
    @3
    cG
    rdgsuc
    eleq1d
    syl5ibr
    syl
    a1d
    findfvcl
end
