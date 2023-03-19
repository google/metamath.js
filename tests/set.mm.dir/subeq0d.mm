include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "subeq0.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem subeq0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subeq0d.3: |- ( ph -> ( A - B ) = 0 )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    cmin
    co
    cc0
    wceq
    #
    cA
    cB
    wceq
    #
    subeq0d.3
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    @0
    @1
    wb
    negidd.1
    pncand.2
    cA
    cB
    subeq0
    syl2anc
    mpbid
end
