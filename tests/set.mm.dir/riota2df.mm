include "wreu.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "cio.mm"
include "wceq.mm"
include "crio.mm"
include "adantr.mm"
include "weu.mm"
include "simpr.mm"
include "df-reu.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "biantrurd.mm"
include "wb.mm"
include "adantlr.mm"
include "bitr3d.mm"
include "nfreu1.mm"
include "nfan.mm"
include "wnf.mm"
include "wnfc.mm"
include "iota2df.mm"
include "df-riota.mm"
include "eqeq1i.mm"
include "syl6bbr.mm"

theorem riota2df
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riota2df.1: |- F/ x ph
  assume riota2df.2: |- ( ph -> F/_ x B )
  assume riota2df.3: |- ( ph -> F/ x ch )
  assume riota2df.4: |- ( ph -> B e. A )
  assume riota2df.5: |- ( ( ph /\ x = B ) -> ( ps <-> ch ) )

  disjoint A x
  assert |- ( ( ph /\ E! x e. A ps ) -> ( ch <-> ( iota_ x e. A ps ) = B ) )

  proof
    wph
    wps
    vx
    cA
    wreu
    #
    wa
    #
    wch
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vx
    cio
    #
    cB
    wceq
    wps
    vx
    cA
    crio
    #
    cB
    wceq
    @1
    @4
    wch
    vx
    cB
    cA
    wph
    cB
    cA
    wcel
    #
    @0
    riota2df.4
    adantr
    #
    @1
    @0
    @4
    vx
    weu
    wph
    @0
    simpr
    wps
    vx
    cA
    df-reu
    sylib
    @1
    @2
    cB
    wceq
    #
    wa
    #
    wps
    @4
    wch
    @10
    @3
    wps
    @10
    @2
    cB
    cA
    @1
    @9
    simpr
    @1
    @7
    @9
    @8
    adantr
    eqeltrd
    biantrurd
    wph
    @9
    wps
    wch
    wb
    @0
    riota2df.5
    adantlr
    bitr3d
    wph
    @0
    vx
    riota2df.1
    wps
    vx
    cA
    nfreu1
    nfan
    wph
    wch
    vx
    wnf
    @0
    riota2df.3
    adantr
    wph
    vx
    cB
    wnfc
    @0
    riota2df.2
    adantr
    iota2df
    @6
    @5
    cB
    wps
    vx
    cA
    df-riota
    eqeq1i
    syl6bbr
end
