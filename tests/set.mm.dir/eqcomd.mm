include "wceq.mm"
include "eqid.mm"
include "eqeq1d.mm"
include "mpbii.mm"

theorem eqcomd
  param wph: wff ph
  param cA: class A
  param cB: class B
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
