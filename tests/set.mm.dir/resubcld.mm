include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "resubcl.mm"
include "syl2anc.mm"

theorem resubcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume renegcld.1: |- ( ph -> A e. RR )
  assume resubcld.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A - B ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cmin
    co
    cr
    wcel
    renegcld.1
    resubcld.2
    cA
    cB
    resubcl
    syl2anc
end
