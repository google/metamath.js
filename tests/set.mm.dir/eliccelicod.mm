include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "eliccxr.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "iccleub.mm"
include "xrleneltd.mm"
include "elicod.mm"

theorem eliccelicod
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliccelicod.a: |- ( ph -> A e. RR* )
  assume eliccelicod.b: |- ( ph -> B e. RR* )
  assume eliccelicod.c: |- ( ph -> C e. ( A [,] B ) )
  assume eliccelicod.d: |- ( ph -> C =/= B )


  assert |- ( ph -> C e. ( A [,) B ) )

  proof
    wph
    cA
    cB
    cC
    eliccelicod.a
    eliccelicod.b
    wph
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    cC
    cxr
    wcel
    eliccelicod.c
    cC
    cA
    cB
    eliccxr
    syl
    #
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @0
    cA
    cC
    cle
    wbr
    eliccelicod.a
    eliccelicod.b
    eliccelicod.c
    cA
    cB
    cC
    iccgelb
    syl3anc
    wph
    cC
    cB
    @1
    eliccelicod.b
    wph
    @2
    @3
    @0
    cC
    cB
    cle
    wbr
    eliccelicod.a
    eliccelicod.b
    eliccelicod.c
    cA
    cB
    cC
    iccleub
    syl3anc
    eliccelicod.d
    xrleneltd
    elicod
end
