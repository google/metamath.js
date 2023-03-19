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
include "cvv.mm"
include "df-itg.mm"
include "sumex.mm"
include "eqeltri.mm"

theorem itgex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vy: setvar y
  let cC: class C


  assert |- S. A B _d x e. _V

  proof
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
    vy
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
    vy
    cv
    #
    cle
    wbr
    wa
    @2
    cc0
    cif
    csb
    cmpt
    citg2
    cfv
    cmul
    co
    #
    vk
    csu
    cvv
    vx
    vy
    cA
    cB
    vk
    df-itg
    @0
    @3
    vk
    sumex
    eqeltri
end
