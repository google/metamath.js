include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cdiv.mm"
include "cre.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "imval.mm"
include "syl.mm"
include "cc0.mm"
include "wne.mm"
include "ine0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "fveq2d.mm"
include "eqtr2d.mm"

theorem reim
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( Re ` A ) = ( Im ` ( _i x. A ) ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cmul
    co
    #
    cim
    cfv
    #
    @1
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    cA
    cre
    cfv
    @0
    @1
    cc
    wcel
    #
    @2
    @4
    wceq
    ci
    cc
    wcel
    #
    @0
    @5
    ax-icn
    ci
    cA
    mulcl
    mpan
    @1
    imval
    syl
    @0
    @3
    cA
    cre
    @0
    @6
    ci
    cc0
    wne
    @3
    cA
    wceq
    ax-icn
    ine0
    cA
    ci
    divcan3
    mp3an23
    fveq2d
    eqtr2d
end
