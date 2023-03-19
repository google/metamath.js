include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "pjpjhth.mm"
include "mp2an.mm"

theorem pjpjhthi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cH: class H
  assume pjpjhth.1: |- A e. ~H
  assume pjpjhth.2: |- H e. CH

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint H x
  disjoint H y
  assert |- E. x e. H E. y e. ( _|_ ` H ) A = ( x +h y )

  proof
    cH
    cch
    wcel
    cA
    chil
    wcel
    cA
    vx
    cv
    vy
    cv
    cva
    co
    wceq
    vy
    cH
    cort
    cfv
    wrex
    vx
    cH
    wrex
    pjpjhth.2
    pjpjhth.1
    vx
    vy
    cA
    cH
    pjpjhth
    mp2an
end
