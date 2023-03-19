include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "subcan2.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem subcan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume subcan2d.4: |- ( ph -> ( A - C ) = ( B - C ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cC
    cmin
    co
    cB
    cC
    cmin
    co
    wceq
    #
    cA
    cB
    wceq
    #
    subcan2d.4
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
    @0
    @1
    wb
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    subcan2
    syl3anc
    mpbid
end
