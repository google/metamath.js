include "wceq.mm"
include "cinf.mm"
include "infeq1.mm"
include "syl.mm"

theorem infeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infeq1d.1: |- ( ph -> B = C )


  assert |- ( ph -> inf ( B , A , R ) = inf ( C , A , R ) )

  proof
    wph
    cB
    cC
    wceq
    cB
    cA
    cR
    cinf
    cC
    cA
    cR
    cinf
    wceq
    infeq1d.1
    cA
    cB
    cC
    cR
    infeq1
    syl
end
