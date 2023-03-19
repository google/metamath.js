include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "sqge0.mm"
include "syl.mm"

theorem sqge0d
  let wph: wff ph
  let cA: class A
  assume resqcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> 0 <_ ( A ^ 2 ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    c2
    cexp
    co
    cle
    wbr
    resqcld.1
    cA
    sqge0
    syl
end
