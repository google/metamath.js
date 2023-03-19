include "wdisj.mm"
include "disjeq1d.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "disjeq2dv.mm"
include "bitrd.mm"

theorem disjeq12d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume disjeq1d.1: |- ( ph -> A = B )
  assume disjeq12d.1: |- ( ph -> C = D )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ph -> ( Disj_ x e. A C <-> Disj_ x e. B D ) )

  proof
    wph
    vx
    cA
    cC
    wdisj
    vx
    cB
    cC
    wdisj
    vx
    cB
    cD
    wdisj
    wph
    vx
    cA
    cB
    cC
    disjeq1d.1
    disjeq1d
    wph
    vx
    cB
    cC
    cD
    wph
    cC
    cD
    wceq
    vx
    cv
    cB
    wcel
    disjeq12d.1
    adantr
    disjeq2dv
    bitrd
end
