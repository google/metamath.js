include "crp.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "rpmulcl.mm"
include "syl2anc.mm"

theorem rpmulcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A x. B ) e. RR+ )

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
    cmul
    co
    crp
    wcel
    rpred.1
    rpaddcld.1
    cA
    cB
    rpmulcl
    syl2anc
end
