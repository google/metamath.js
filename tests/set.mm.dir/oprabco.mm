include "wfn.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "adantl.mm"
include "wceq.mm"
include "a1i.mm"
include "cmpt.mm"
include "dffn5.mm"
include "biimpi.mm"
include "fveq2.mm"
include "fmpt2co.mm"
include "syl6reqr.mm"

theorem oprabco
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let vz: setvar z
  assume oprabco.1: |- ( ( x e. A /\ y e. B ) -> C e. D )
  assume oprabco.2: |- F = ( x e. A , y e. B |-> C )
  assume oprabco.3: |- G = ( x e. A , y e. B |-> ( H ` C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  disjoint H x
  disjoint H y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint D z
  disjoint H z
  disjoint C z
  assert |- ( H Fn D -> G = ( H o. F ) )

  proof
    cH
    cD
    wfn
    #
    cH
    cF
    ccom
    vx
    vy
    cA
    cB
    cC
    cH
    cfv
    #
    cmpt2
    cG
    @0
    vx
    vy
    vz
    cA
    cB
    cD
    cC
    vz
    cv
    #
    cH
    cfv
    #
    @1
    cF
    cH
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    cC
    cD
    wcel
    @0
    oprabco.1
    adantl
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    wceq
    @0
    oprabco.2
    a1i
    @0
    cH
    vz
    cD
    @3
    cmpt
    wceq
    vz
    cD
    cH
    dffn5
    biimpi
    @2
    cC
    cH
    fveq2
    fmpt2co
    oprabco.3
    syl6reqr
end
