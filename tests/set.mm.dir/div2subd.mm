include "cc.mm"
include "wcel.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "div2sub.mm"
include "syl23anc.mm"

theorem div2subd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume div2subd.1: |- ( ph -> A e. CC )
  assume div2subd.2: |- ( ph -> B e. CC )
  assume div2subd.3: |- ( ph -> C e. CC )
  assume div2subd.4: |- ( ph -> D e. CC )
  assume div2subd.5: |- ( ph -> C =/= D )


  assert |- ( ph -> ( ( A - B ) / ( C - D ) ) = ( ( B - A ) / ( D - C ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cD
    cc
    wcel
    cC
    cD
    wne
    cA
    cB
    cmin
    co
    cC
    cD
    cmin
    co
    cdiv
    co
    cB
    cA
    cmin
    co
    cD
    cC
    cmin
    co
    cdiv
    co
    wceq
    div2subd.1
    div2subd.2
    div2subd.3
    div2subd.4
    div2subd.5
    cA
    cB
    cC
    cD
    div2sub
    syl23anc
end
