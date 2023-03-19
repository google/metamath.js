include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "cva.mm"
include "cxp.mm"
include "cima.mm"
include "chil.mm"
include "shsval.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "wss.mm"
include "ax-hfvadd.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "syl6eqss.mm"

theorem shsss
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A +H B ) C_ ~H )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    wa
    cA
    cB
    cph
    co
    cva
    cA
    cB
    cxp
    #
    cima
    #
    chil
    cA
    cB
    shsval
    @1
    cva
    crn
    #
    chil
    cva
    @0
    imassrn
    chil
    chil
    cxp
    #
    chil
    cva
    wf
    @2
    chil
    wss
    ax-hfvadd
    @3
    chil
    cva
    frn
    ax-mp
    sstri
    syl6eqss
end
