include "co1.mm"
include "wcel.mm"
include "cres.mm"
include "cabs.mm"
include "ccom.mm"
include "clo1.mm"
include "resco.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "wb.mm"
include "o1f.mm"
include "lo1o1.mm"
include "syl.mm"
include "ibi.mm"
include "lo1res.mm"
include "syl5eqelr.mm"
include "cin.mm"
include "fresin.mm"
include "3syl.mm"
include "mpbird.mm"

theorem o1res
  let cA: class A
  let cF: class F
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( F e. O(1) -> ( F |` A ) e. O(1) )

  proof
    cF
    co1
    wcel
    #
    cF
    cA
    cres
    #
    co1
    wcel
    #
    cabs
    @1
    ccom
    #
    clo1
    wcel
    #
    @0
    @3
    cabs
    cF
    ccom
    #
    cA
    cres
    #
    clo1
    cabs
    cF
    cA
    resco
    @0
    @5
    clo1
    wcel
    #
    @6
    clo1
    wcel
    @0
    @7
    @0
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @0
    @7
    wb
    cF
    o1f
    #
    @8
    cF
    lo1o1
    syl
    ibi
    cA
    @5
    lo1res
    syl
    syl5eqelr
    @0
    @9
    @8
    cA
    cin
    #
    cc
    @1
    wf
    @2
    @4
    wb
    @10
    @8
    cc
    cF
    cA
    fresin
    @11
    @1
    lo1o1
    3syl
    mpbird
end
