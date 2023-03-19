include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "c2.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "ciun.mm"
include "wdisj.mm"
include "wtru.mm"
include "oveq1.mm"
include "oveq2.mm"
include "weq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "wcel.mm"
include "wa.mm"
include "wspthneq1eq2.mm"
include "simpld.mm"
include "3adant1.mm"
include "disjiund.mm"
include "trud.mm"

theorem 2wspiundisj
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cA: class A
  let vc: setvar c
  let vt: setvar t
  let vd: setvar d

  disjoint G b
  disjoint V b
  disjoint G a
  disjoint V a
  disjoint a b
  disjoint A b
  disjoint A c
  disjoint A t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint G c
  disjoint G t
  disjoint V c
  disjoint V t
  disjoint G d
  disjoint a d
  disjoint V d
  disjoint a c
  disjoint a t
  disjoint b d
  disjoint c d
  disjoint d t
  assert |- Disj_ a e. V U_ b e. ( V \ { a } ) ( a ( 2 WSPathsNOn G ) b )

  proof
    va
    cV
    vb
    cV
    va
    cv
    #
    csn
    #
    cdif
    #
    @0
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
    ciun
    wdisj
    wtru
    vt
    @5
    vc
    cv
    #
    @3
    @4
    co
    @6
    vd
    cv
    #
    @4
    co
    #
    cV
    @2
    cV
    @6
    csn
    #
    cdif
    va
    vb
    vc
    vd
    @0
    @6
    @3
    @4
    oveq1
    @3
    @7
    @6
    @4
    oveq2
    va
    vc
    weq
    #
    @1
    @9
    cV
    @0
    @6
    sneq
    difeq2d
    vt
    cv
    #
    @5
    wcel
    #
    @11
    @8
    wcel
    #
    @10
    wtru
    @12
    @13
    wa
    @10
    vb
    vd
    weq
    @0
    @3
    @6
    @7
    @11
    cG
    c2
    wspthneq1eq2
    simpld
    3adant1
    disjiund
    trud
end
