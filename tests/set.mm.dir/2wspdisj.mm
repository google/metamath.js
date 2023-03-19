include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "c2.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "wdisj.mm"
include "wtru.mm"
include "oveq2.mm"
include "wcel.mm"
include "weq.mm"
include "wa.mm"
include "wceq.mm"
include "wspthneq1eq2.mm"
include "simprd.mm"
include "3adant1.mm"
include "disjord.mm"
include "trud.mm"

theorem 2wspdisj
  let cA: class A
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let vt: setvar t

  disjoint A b
  disjoint G b
  disjoint V b
  disjoint A c
  disjoint A t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint G c
  disjoint G t
  disjoint V c
  disjoint V t
  assert |- Disj_ b e. ( V \ { A } ) ( A ( 2 WSPathsNOn G ) b )

  proof
    vb
    cV
    cA
    csn
    cdif
    #
    cA
    vb
    cv
    #
    c2
    cG
    cwwspthsnon
    co
    #
    co
    #
    wdisj
    wtru
    vt
    @3
    cA
    vc
    cv
    #
    @2
    co
    #
    @0
    vb
    vc
    @1
    @4
    cA
    @2
    oveq2
    vt
    cv
    #
    @3
    wcel
    #
    @6
    @5
    wcel
    #
    vb
    vc
    weq
    #
    wtru
    @7
    @8
    wa
    cA
    cA
    wceq
    @9
    cA
    @1
    cA
    @4
    @6
    cG
    c2
    wspthneq1eq2
    simprd
    3adant1
    disjord
    trud
end
