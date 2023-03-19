include "csh.mm"
include "wcel.mm"
include "cph.mm"
include "co.mm"
include "cv.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "shsel.mm"
include "mp2an.mm"

theorem shseli
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vz: setvar z
  let cD: class D
  assume shscl.1: |- A e. SH
  assume shscl.2: |- B e. SH

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
  assert |- ( C e. ( A +H B ) <-> E. x e. A E. y e. B C = ( x +h y ) )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    cC
    cA
    cB
    cph
    co
    wcel
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
    wb
    shscl.1
    shscl.2
    vx
    vy
    cA
    cB
    cC
    shsel
    mp2an
end
