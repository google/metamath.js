include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "subcan.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem subcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume subcand.4: |- ( ph -> ( A - B ) = ( A - C ) )


  assert |- ( ph -> B = C )

  proof
    wph
    cA
    cB
    cmin
    co
    cA
    cC
    cmin
    co
    wceq
    #
    cB
    cC
    wceq
    #
    subcand.4
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
    subcan
    syl3anc
    mpbid
end
