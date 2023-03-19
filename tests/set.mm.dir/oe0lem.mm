include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "ex.mm"
include "adantl.mm"
include "wne.mm"
include "wb.mm"
include "on0eln0.mm"
include "adantr.mm"
include "sylbird.mm"
include "pm2.61dne.mm"

theorem oe0lem
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  assume oe0lem.1: |- ( ( ph /\ A = (/) ) -> ps )
  assume oe0lem.2: |- ( ( ( A e. On /\ ph ) /\ (/) e. A ) -> ps )


  assert |- ( ( A e. On /\ ph ) -> ps )

  proof
    cA
    con0
    wcel
    #
    wph
    wa
    #
    wps
    cA
    c0
    wph
    cA
    c0
    wceq
    #
    wps
    wi
    @0
    wph
    @2
    wps
    oe0lem.1
    ex
    adantl
    @1
    cA
    c0
    wne
    #
    c0
    cA
    wcel
    #
    wps
    @0
    @4
    @3
    wb
    wph
    cA
    on0eln0
    adantr
    @1
    @4
    wps
    oe0lem.2
    ex
    sylbird
    pm2.61dne
end
