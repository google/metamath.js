include "wa.mm"
include "wceq.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wss.mm"
include "adantr.mm"
include "eqsstr3d.mm"

theorem bnj1241
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj1241.1: |- ( ph -> A C_ B )
  assume bnj1241.2: |- ( ps -> C = A )


  assert |- ( ( ph /\ ps ) -> C C_ B )

  proof
    wph
    wps
    wa
    cC
    cA
    cB
    wps
    cA
    cC
    wceq
    wph
    wps
    cC
    cA
    bnj1241.2
    eqcomd
    adantl
    wph
    cA
    cB
    wss
    wps
    bnj1241.1
    adantr
    eqsstr3d
end
