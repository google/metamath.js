include "weu.mm"
include "wral.mm"
include "wfn.mm"
include "rgen.mm"
include "fnopabg.mm"
include "mpbi.mm"

theorem fnopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  assume fnopab.1: |- ( x e. A -> E! y ph )
  assume fnopab.2: |- F = { <. x , y >. | ( x e. A /\ ph ) }

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- F Fn A

  proof
    wph
    vy
    weu
    #
    vx
    cA
    wral
    cF
    cA
    wfn
    @0
    vx
    cA
    fnopab.1
    rgen
    wph
    vx
    vy
    cA
    cF
    fnopab.2
    fnopabg
    mpbi
end
