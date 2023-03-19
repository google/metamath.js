include "wfn.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "adantl.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "dffn5.mm"
include "biimpi.mm"
include "fveq2.mm"
include "fmptco.mm"
include "syl6reqr.mm"

theorem fnopabco
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  assume fnopabco.1: |- ( x e. A -> B e. C )
  assume fnopabco.2: |- F = { <. x , y >. | ( x e. A /\ y = B ) }
  assume fnopabco.3: |- G = { <. x , y >. | ( x e. A /\ y = ( H ` B ) ) }

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint B y
  disjoint H x
  disjoint H y
  disjoint A x
  disjoint A y
  assert |- ( H Fn C -> G = ( H o. F ) )

  proof
    cH
    cC
    wfn
    #
    cH
    cF
    ccom
    vx
    cA
    cB
    cH
    cfv
    #
    cmpt
    #
    cG
    @0
    vx
    vy
    cA
    cC
    cB
    vy
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
    #
    cB
    cC
    wcel
    @0
    fnopabco.1
    adantl
    cF
    vx
    cA
    cB
    cmpt
    #
    wceq
    @0
    cF
    @5
    @3
    cB
    wceq
    wa
    vx
    vy
    copab
    @6
    fnopabco.2
    vx
    vy
    cA
    cB
    df-mpt
    eqtr4i
    a1i
    @0
    cH
    vy
    cC
    @4
    cmpt
    wceq
    vy
    cC
    cH
    dffn5
    biimpi
    @3
    cB
    cH
    fveq2
    fmptco
    cG
    @5
    @3
    @1
    wceq
    wa
    vx
    vy
    copab
    @2
    fnopabco.3
    vx
    vy
    cA
    @1
    df-mpt
    eqtr4i
    syl6reqr
end
