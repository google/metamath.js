include "citg.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "csb.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "df-itg.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "nfov.mm"
include "nfsum.mm"
include "nfcxfr.mm"

theorem nfitg1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vz: setvar z


  assert |- F/_ x S. A B _d x

  proof
    vx
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
    vz
    cB
    @1
    cdiv
    co
    cre
    cfv
    vx
    cv
    cA
    wcel
    cc0
    vz
    cv
    #
    cle
    wbr
    wa
    @2
    cc0
    cif
    csb
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
    vz
    cA
    cB
    vk
    df-itg
    vx
    @0
    @6
    vk
    vx
    @0
    nfcv
    vx
    @1
    @5
    cmul
    vx
    @1
    nfcv
    vx
    cmul
    nfcv
    vx
    @4
    citg2
    vx
    citg2
    nfcv
    vx
    cr
    @3
    nfmpt1
    nffv
    nfov
    nfsum
    nfcxfr
end
