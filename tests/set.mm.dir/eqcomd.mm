include "wceq.mm"
include "eqid.mm"
include "eqeq1d.mm"
include "mpbii.mm"

theorem eqcomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume eqcomd.1: |- ( ph -> A = B )


  assert |- ( ph -> B = A )

  proof
    wph
    cA
    cA
    wceq
    cB
    cA
    wceq
    cA
    eqid
    wph
    cA
    cB
    cA
    eqcomd.1
    eqeq1d
    mpbii
end
