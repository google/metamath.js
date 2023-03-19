include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "mtbi.mm"
include "imnani.mm"
include "nne.mm"
include "sylib.mm"

theorem bnj1541
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume bnj1541.1: |- ( ph <-> ( ps /\ A =/= B ) )
  assume bnj1541.2: |- -. ph


  assert |- ( ps -> A = B )

  proof
    wps
    cA
    cB
    wne
    #
    wn
    cA
    cB
    wceq
    wps
    @0
    wph
    wps
    @0
    wa
    bnj1541.2
    bnj1541.1
    mtbi
    imnani
    cA
    cB
    nne
    sylib
end
