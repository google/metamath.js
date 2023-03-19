include "crp.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "rpdivcl.mm"
include "syl2anc.mm"

theorem rpdivcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A / B ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    cB
    crp
    wcel
    cA
    cB
    cdiv
    co
    crp
    wcel
    rpred.1
    rpaddcld.1
    cA
    cB
    rpdivcl
    syl2anc
end
