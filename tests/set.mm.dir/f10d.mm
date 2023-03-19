include "cdm.mm"
include "wf1.mm"
include "c0.mm"
include "f10.mm"
include "wceq.mm"
include "wb.mm"
include "dm0.mm"
include "f1eq2.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "dmeqd.mm"
include "eqidd.mm"
include "f1eq123d.mm"
include "mpbiri.mm"

theorem f10d
  let wph: wff ph
  let cA: class A
  let cF: class F
  assume f10d.f: |- ( ph -> F = (/) )


  assert |- ( ph -> F : dom F -1-1-> A )

  proof
    wph
    cF
    cdm
    #
    cA
    cF
    wf1
    c0
    cdm
    #
    cA
    c0
    wf1
    #
    @2
    c0
    cA
    c0
    wf1
    #
    cA
    f10
    @1
    c0
    wceq
    @2
    @3
    wb
    dm0
    @1
    c0
    cA
    c0
    f1eq2
    ax-mp
    mpbir
    wph
    @0
    @1
    cA
    cA
    cF
    c0
    f10d.f
    wph
    cF
    c0
    f10d.f
    dmeqd
    wph
    cA
    eqidd
    f1eq123d
    mpbiri
end
