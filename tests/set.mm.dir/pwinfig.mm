include "cv.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "wral.mm"
include "cfn.mm"
include "wn.mm"
include "cdif.mm"
include "pwelg.mm"
include "wb.mm"
include "pwfi.mm"
include "notbii.mm"
include "a1i.mm"
include "anbi12d.mm"
include "eldif.mm"
include "3bitr4g.mm"

theorem pwinfig
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A. x e. B ( U. x e. B /\ ~P x e. B ) -> ( A e. ( B \ Fin ) <-> ~P A e. ( B \ Fin ) ) )

  proof
    vx
    cv
    #
    cuni
    cB
    wcel
    @0
    cpw
    cB
    wcel
    wa
    vx
    cB
    wral
    #
    cA
    cB
    wcel
    #
    cA
    cfn
    wcel
    #
    wn
    #
    wa
    cA
    cpw
    #
    cB
    wcel
    #
    @5
    cfn
    wcel
    #
    wn
    #
    wa
    cA
    cB
    cfn
    cdif
    #
    wcel
    @5
    @9
    wcel
    @1
    @2
    @6
    @4
    @8
    vx
    cA
    cB
    pwelg
    @4
    @8
    wb
    @1
    @3
    @7
    cA
    pwfi
    notbii
    a1i
    anbi12d
    cA
    cB
    cfn
    eldif
    @5
    cB
    cfn
    eldif
    3bitr4g
end
