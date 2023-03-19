include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "wb.mm"
include "addsubeq4.mm"
include "syl22anc.mm"

theorem addsubeq4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume addsub4d.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A + B ) = ( C + D ) <-> ( C - A ) = ( B - D ) ) )

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
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    wceq
    cC
    cA
    cmin
    co
    cB
    cD
    cmin
    co
    wceq
    wb
    negidd.1
    pncand.2
    subaddd.3
    addsub4d.4
    cA
    cB
    cC
    cD
    addsubeq4
    syl22anc
end
