include "citg.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "eqid.mm"
include "dfitg.mm"
include "nfcv.mm"
include "nfcri.mm"
include "nfov.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfif.mm"
include "nfmpt.mm"
include "nfsum.mm"
include "nfcxfr.mm"

theorem nfitg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume nfitg.1: |- F/_ y A
  assume nfitg.2: |- F/_ y B

  disjoint x y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint B k
  assert |- F/_ y S. A B _d x

  proof
    vy
    vx
    cA
    cB
    citg
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    cexp
    co
    #
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    @1
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @4
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    vx
    cA
    cB
    @4
    vk
    @4
    eqid
    dfitg
    vy
    @0
    @10
    vk
    vy
    @0
    nfcv
    vy
    @1
    @9
    cmul
    vy
    @1
    nfcv
    #
    vy
    cmul
    nfcv
    vy
    @8
    citg2
    vy
    citg2
    nfcv
    vy
    vx
    cr
    @7
    vy
    cr
    nfcv
    @6
    vy
    @4
    cc0
    @2
    @5
    vy
    vy
    vx
    cA
    nfitg.1
    nfcri
    vy
    cc0
    @4
    cle
    vy
    cc0
    nfcv
    #
    vy
    cle
    nfcv
    vy
    @3
    cre
    vy
    cre
    nfcv
    vy
    cB
    @1
    cdiv
    nfitg.2
    vy
    cdiv
    nfcv
    @11
    nfov
    nffv
    #
    nfbr
    nfan
    @13
    @12
    nfif
    nfmpt
    nffv
    nfov
    nfsum
    nfcxfr
end
