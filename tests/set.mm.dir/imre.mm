include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cre.mm"
include "cneg.mm"
include "cmul.mm"
include "imval.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "ax-icn.mm"
include "ine0.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "irec.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem imre
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( Im ` A ) = ( Re ` ( -u _i x. A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cim
    cfv
    cA
    ci
    cdiv
    co
    #
    cre
    cfv
    ci
    cneg
    #
    cA
    cmul
    co
    #
    cre
    cfv
    cA
    imval
    @0
    @1
    @3
    cre
    @0
    @1
    c1
    ci
    cdiv
    co
    #
    cA
    cmul
    co
    #
    @3
    @0
    ci
    cc
    wcel
    ci
    cc0
    wne
    @1
    @5
    wceq
    ax-icn
    ine0
    cA
    ci
    divrec2
    mp3an23
    @4
    @2
    cA
    cmul
    irec
    oveq1i
    syl6eq
    fveq2d
    eqtrd
end
