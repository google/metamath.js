include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "jca.mm"
include "cxr.mm"
include "wb.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem eliccxrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliccxrd.1: |- ( ph -> A e. RR* )
  assume eliccxrd.2: |- ( ph -> B e. RR* )
  assume eliccxrd.3: |- ( ph -> C e. RR* )
  assume eliccxrd.4: |- ( ph -> A <_ C )
  assume eliccxrd.5: |- ( ph -> C <_ B )


  assert |- ( ph -> C e. ( A [,] B ) )

  proof
    wph
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    wa
    #
    wph
    @1
    @2
    eliccxrd.4
    eliccxrd.5
    jca
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    @0
    @3
    wb
    eliccxrd.1
    eliccxrd.2
    eliccxrd.3
    cA
    cB
    cC
    elicc4
    syl3anc
    mpbird
end
