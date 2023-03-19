include "cif.mm"
include "wceq.mm"
include "wn.mm"
include "iftrue.mm"
include "con3i.mm"
include "iffalsed.mm"
include "orri.mm"

theorem ifeqor
  let wph: wff ph
  let cA: class A
  let cB: class B


  assert |- ( if ( ph , A , B ) = A \/ if ( ph , A , B ) = B )

  proof
    wph
    cA
    cB
    cif
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    @1
    wn
    wph
    cA
    cB
    wph
    @1
    wph
    cA
    cB
    iftrue
    con3i
    iffalsed
    orri
end
