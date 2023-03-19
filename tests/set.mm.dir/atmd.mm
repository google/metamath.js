include "cat.mm"
include "wcel.mm"
include "cv.mm"
include "cmd.mm"
include "wbr.mm"
include "cch.mm"
include "wral.mm"
include "cdmd.mm"
include "atdmd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "atelch.mm"
include "mddmd2.mm"
include "syl.mm"
include "mpbird.mm"
include "breq2.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem atmd
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. HAtoms /\ B e. CH ) -> A MH B )

  proof
    cA
    cat
    wcel
    #
    cA
    vx
    cv
    #
    cmd
    wbr
    #
    vx
    cch
    wral
    #
    cB
    cch
    wcel
    cA
    cB
    cmd
    wbr
    #
    @0
    @3
    cA
    @1
    cdmd
    wbr
    #
    vx
    cch
    wral
    #
    @0
    @5
    vx
    cch
    cA
    @1
    atdmd
    ralrimiva
    @0
    cA
    cch
    wcel
    @3
    @6
    wb
    cA
    atelch
    vx
    cA
    mddmd2
    syl
    mpbird
    @2
    @4
    vx
    cB
    cch
    @1
    cB
    cA
    cmd
    breq2
    rspcv
    mpan9
end
