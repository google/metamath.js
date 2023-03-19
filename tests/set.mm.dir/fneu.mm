include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "funmo.mm"
include "adantr.mm"
include "wex.mm"
include "wb.mm"
include "eldmg.mm"
include "ibi.mm"
include "adantl.mm"
include "exmoeu2.mm"
include "syl.mm"
include "mpbid.mm"
include "funfni.mm"

theorem fneu
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint F y
  disjoint B y
  assert |- ( ( F Fn A /\ B e. A ) -> E! y B F y )

  proof
    cB
    vy
    cv
    cF
    wbr
    #
    vy
    weu
    #
    cA
    cB
    cF
    cF
    wfun
    #
    cB
    cF
    cdm
    #
    wcel
    #
    wa
    #
    @0
    vy
    wmo
    #
    @1
    @2
    @6
    @4
    vy
    cB
    cF
    funmo
    adantr
    @5
    @0
    vy
    wex
    #
    @6
    @1
    wb
    @4
    @7
    @2
    @4
    @7
    vy
    cB
    cF
    @3
    eldmg
    ibi
    adantl
    @0
    vy
    exmoeu2
    syl
    mpbid
    funfni
end
