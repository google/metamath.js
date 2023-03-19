include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "sqgt0.mm"
include "syl2anc.mm"

theorem sqgt0d
  let wph: wff ph
  let cA: class A
  assume resqcld.1: |- ( ph -> A e. RR )
  assume sqgt0d.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> 0 < ( A ^ 2 ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    wne
    cc0
    cA
    c2
    cexp
    co
    clt
    wbr
    resqcld.1
    sqgt0d.2
    cA
    sqgt0
    syl2anc
end
