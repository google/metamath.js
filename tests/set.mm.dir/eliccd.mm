include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"

theorem eliccd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliccd.1: |- ( ph -> A e. RR )
  assume eliccd.2: |- ( ph -> B e. RR )
  assume eliccd.3: |- ( ph -> C e. RR )
  assume eliccd.4: |- ( ph -> A <_ C )
  assume eliccd.5: |- ( ph -> C <_ B )


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
    cC
    cr
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
    eliccd.3
    eliccd.4
    eliccd.5
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    @2
    @3
    w3a
    wb
    eliccd.1
    eliccd.2
    cA
    cB
    cC
    elicc2
    syl2anc
    mpbir3and
end
