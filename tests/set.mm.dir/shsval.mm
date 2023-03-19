include "csh.mm"
include "cva.mm"
include "cv.mm"
include "cxp.mm"
include "cima.mm"
include "cph.mm"
include "wceq.mm"
include "wa.mm"
include "xpeq12.mm"
include "imaeq2d.mm"
include "df-shs.mm"
include "cablo.mm"
include "wcel.mm"
include "cvv.mm"
include "hilablo.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "ovmpt2a.mm"

theorem shsval
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A +H B ) = ( +h " ( A X. B ) ) )

  proof
    vx
    vy
    cA
    cB
    csh
    csh
    cva
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cima
    cva
    cA
    cB
    cxp
    #
    cima
    #
    cph
    @0
    cA
    wceq
    @1
    cB
    wceq
    wa
    @2
    @3
    cva
    @0
    cA
    @1
    cB
    xpeq12
    imaeq2d
    vx
    vy
    df-shs
    cva
    cablo
    wcel
    @4
    cvv
    wcel
    hilablo
    cva
    @3
    cablo
    imaexg
    ax-mp
    ovmpt2a
end
