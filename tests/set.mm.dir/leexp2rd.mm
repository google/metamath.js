include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "leexp2r.mm"
include "syl32anc.mm"

theorem leexp2rd
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume resqcld.1: |- ( ph -> A e. RR )
  assume leexp2rd.2: |- ( ph -> M e. NN0 )
  assume leexp2rd.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume leexp2rd.4: |- ( ph -> 0 <_ A )
  assume leexp2rd.5: |- ( ph -> A <_ 1 )


  assert |- ( ph -> ( A ^ N ) <_ ( A ^ M ) )

  proof
    wph
    cA
    cr
    wcel
    cM
    cn0
    wcel
    cN
    cM
    cuz
    cfv
    wcel
    cc0
    cA
    cle
    wbr
    cA
    c1
    cle
    wbr
    cA
    cN
    cexp
    co
    cA
    cM
    cexp
    co
    cle
    wbr
    resqcld.1
    leexp2rd.2
    leexp2rd.3
    leexp2rd.4
    leexp2rd.5
    cA
    cM
    cN
    leexp2r
    syl32anc
end
