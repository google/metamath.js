include "wa.mm"
include "wsbc.mm"
include "wceq.mm"
include "adantr.mm"
include "sylibr.mm"
include "adantl.mm"
include "sbceq1dd.mm"
include "sylib.mm"

theorem sbceq1ddi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume sbceq1ddi.1: |- ( ph -> A = B )
  assume sbceq1ddi.2: |- ( ps -> th )
  assume sbceq1ddi.3: |- ( [. A / x ]. ch <-> th )
  assume sbceq1ddi.4: |- ( [. B / x ]. ch <-> et )


  assert |- ( ( ph /\ ps ) -> et )

  proof
    wph
    wps
    wa
    #
    wch
    vx
    cB
    wsbc
    wet
    @0
    wch
    vx
    cA
    cB
    wph
    cA
    cB
    wceq
    wps
    sbceq1ddi.1
    adantr
    wps
    wch
    vx
    cA
    wsbc
    #
    wph
    wps
    wth
    @1
    sbceq1ddi.2
    sbceq1ddi.3
    sylibr
    adantl
    sbceq1dd
    sbceq1ddi.4
    sylib
end
