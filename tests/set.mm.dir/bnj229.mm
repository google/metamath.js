include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "com.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "bnj213.mm"
include "bnj226.mm"
include "wi.mm"
include "bnj222.mm"
include "bnj228.mm"
include "adantl.mm"
include "wb.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "adantr.mm"
include "mpbid.mm"
include "3impb.mm"
include "impcom.mm"
include "bnj1262.mm"

theorem bnj229
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  assume bnj229.1: |- ( ps <-> A. i e. _om ( suc i e. N -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )

  disjoint A i
  disjoint A m
  disjoint A y
  disjoint i m
  disjoint i y
  disjoint m y
  disjoint F i
  disjoint F m
  disjoint F y
  disjoint N i
  disjoint N m
  disjoint R i
  disjoint R m
  assert |- ( ( n e. N /\ ( suc m = n /\ m e. _om /\ ps ) ) -> ( F ` n ) C_ A )

  proof
    vn
    cv
    #
    cN
    wcel
    #
    vm
    cv
    #
    csuc
    #
    @0
    wceq
    #
    @2
    com
    wcel
    #
    wps
    w3a
    #
    wa
    vy
    @2
    cF
    cfv
    #
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    ciun
    #
    cA
    @0
    cF
    cfv
    #
    vy
    @7
    @9
    cA
    cA
    cR
    @8
    bnj213
    bnj226
    @6
    @1
    @11
    @10
    wceq
    #
    @4
    @5
    wps
    @1
    @12
    wi
    #
    @4
    @5
    wps
    wa
    #
    wa
    @3
    cN
    wcel
    #
    @3
    cF
    cfv
    #
    @10
    wceq
    #
    wi
    #
    @13
    @14
    @18
    @4
    wps
    @18
    vm
    com
    wps
    vy
    cA
    cR
    vi
    vm
    cF
    cN
    bnj229.1
    bnj222
    bnj228
    adantl
    @4
    @18
    @13
    wb
    @14
    @4
    @15
    @1
    @17
    @12
    @3
    @0
    cN
    eleq1
    @4
    @16
    @11
    @10
    @3
    @0
    cF
    fveq2
    eqeq1d
    imbi12d
    adantr
    mpbid
    3impb
    impcom
    bnj1262
end
