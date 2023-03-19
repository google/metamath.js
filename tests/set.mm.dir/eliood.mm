include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"

theorem eliood
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliood.1: |- ( ph -> A e. RR* )
  assume eliood.2: |- ( ph -> B e. RR* )
  assume eliood.3: |- ( ph -> C e. RR )
  assume eliood.4: |- ( ph -> A < C )
  assume eliood.5: |- ( ph -> C < B )


  assert |- ( ph -> C e. ( A (,) B ) )

  proof
    wph
    cC
    cA
    cB
    cioo
    co
    wcel
    #
    cC
    cr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    eliood.3
    eliood.4
    eliood.5
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @1
    @2
    @3
    w3a
    wb
    eliood.1
    eliood.2
    cA
    cB
    cC
    elioo2
    syl2anc
    mpbir3and
end
