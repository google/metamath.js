include "cico.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "elico1.mm"
include "syl2anc.mm"
include "mpbir3and.mm"

theorem elicod
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume elicod.a: |- ( ph -> A e. RR* )
  assume elicod.b: |- ( ph -> B e. RR* )
  assume elicod.3: |- ( ph -> C e. RR* )
  assume elicod.4: |- ( ph -> A <_ C )
  assume elicod.5: |- ( ph -> C < B )


  assert |- ( ph -> C e. ( A [,) B ) )

  proof
    wph
    cC
    cA
    cB
    cico
    co
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    elicod.3
    elicod.4
    elicod.5
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
    elicod.a
    elicod.b
    cA
    cB
    cC
    elico1
    syl2anc
    mpbir3and
end
