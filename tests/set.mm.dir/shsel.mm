include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "cva.mm"
include "cxp.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "shsval.mm"
include "eleq2d.mm"
include "chil.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "wf.mm"
include "ax-hfvadd.mm"
include "ffn.mm"
include "ax-mp.mm"
include "shss.mm"
include "xpss12.mm"
include "syl2an.mm"
include "ovelimab.mm"
include "sylancr.mm"
include "bitrd.mm"

theorem shsel
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vz: setvar z
  let cD: class D

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D x
  disjoint D y
  assert |- ( ( A e. SH /\ B e. SH ) -> ( C e. ( A +H B ) <-> E. x e. A E. y e. B C = ( x +h y ) ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cph
    co
    #
    wcel
    cC
    cva
    cA
    cB
    cxp
    #
    cima
    #
    wcel
    #
    cC
    vx
    cv
    vy
    cv
    cva
    co
    wceq
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @2
    @3
    @5
    cC
    cA
    cB
    shsval
    eleq2d
    @2
    cva
    chil
    chil
    cxp
    #
    wfn
    #
    @4
    @8
    wss
    #
    @6
    @7
    wb
    @8
    chil
    cva
    wf
    @9
    ax-hfvadd
    @8
    chil
    cva
    ffn
    ax-mp
    @0
    cA
    chil
    wss
    cB
    chil
    wss
    @10
    @1
    cA
    shss
    cB
    shss
    cA
    chil
    cB
    chil
    xpss12
    syl2an
    vx
    vy
    @8
    cA
    cB
    cC
    cva
    ovelimab
    sylancr
    bitrd
end
