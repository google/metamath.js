include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "leexp2a.mm"
include "syl3anc.mm"

theorem leexp2ad
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume resqcld.1: |- ( ph -> A e. RR )
  assume leexp2ad.2: |- ( ph -> 1 <_ A )
  assume leexp2ad.3: |- ( ph -> N e. ( ZZ>= ` M ) )


  assert |- ( ph -> ( A ^ M ) <_ ( A ^ N ) )

  proof
    wph
    cA
    cr
    wcel
    c1
    cA
    cle
    wbr
    cN
    cM
    cuz
    cfv
    wcel
    cA
    cM
    cexp
    co
    cA
    cN
    cexp
    co
    cle
    wbr
    resqcld.1
    leexp2ad.2
    leexp2ad.3
    cA
    cM
    cN
    leexp2a
    syl3anc
end
