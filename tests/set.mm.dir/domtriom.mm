include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "domnsym.mm"
include "cfn.mm"
include "wcel.mm"
include "isfinite.mm"
include "cv.mm"
include "wss.mm"
include "cpw.mm"
include "cen.mm"
include "wa.mm"
include "cab.mm"
include "cfv.mm"
include "ciun.mm"
include "cdif.mm"
include "cmpt.mm"
include "eqid.mm"
include "weq.mm"
include "fveq2.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "difeq12d.mm"
include "cbvmptv.mm"
include "domtriomlem.mm"
include "sylnbir.mm"
include "impbii.mm"

theorem domtriom
  let cA: class A
  let vb: setvar b
  let vn: setvar n
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  assume domtriom.1: |- A e. _V


  assert |- ( _om ~<_ A <-> -. A ~< _om )

  proof
    com
    cA
    cdom
    wbr
    #
    cA
    com
    csdm
    wbr
    #
    wn
    com
    cA
    domnsym
    @1
    cA
    cfn
    wcel
    @0
    cA
    isfinite
    vy
    cA
    vy
    cv
    #
    cA
    wss
    @2
    vn
    cv
    #
    cpw
    cen
    wbr
    wa
    vy
    cab
    #
    vm
    com
    vm
    cv
    #
    vb
    cv
    #
    cfv
    #
    vj
    @5
    vj
    cv
    #
    @6
    cfv
    #
    ciun
    #
    cdif
    #
    cmpt
    vk
    vn
    vb
    domtriom.1
    @4
    eqid
    vm
    vn
    com
    @11
    @3
    @6
    cfv
    #
    vk
    @3
    vk
    cv
    #
    @6
    cfv
    #
    ciun
    #
    cdif
    vm
    vn
    weq
    #
    @7
    @12
    @10
    @15
    @5
    @3
    @6
    fveq2
    @16
    @10
    vk
    @5
    @14
    ciun
    @15
    vj
    vk
    @5
    @9
    @14
    @8
    @13
    @6
    fveq2
    cbviunv
    vk
    @5
    @3
    @14
    iuneq1
    syl5eq
    difeq12d
    cbvmptv
    domtriomlem
    sylnbir
    impbii
end
