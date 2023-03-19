include "cio.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "simpr.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "weu.mm"
include "iota1.mm"
include "syl.mm"
include "wnfc.mm"
include "nfiota1.mm"
include "a1i.mm"
include "nfeqd.mm"
include "nfbid.mm"
include "vtocldf.mm"

theorem iota2df
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cB: class B
  let cV: class V
  assume iota2df.1: |- ( ph -> B e. V )
  assume iota2df.2: |- ( ph -> E! x ps )
  assume iota2df.3: |- ( ( ph /\ x = B ) -> ( ps <-> ch ) )
  assume iota2df.4: |- F/ x ph
  assume iota2df.5: |- ( ph -> F/ x ch )
  assume iota2df.6: |- ( ph -> F/_ x B )


  assert |- ( ph -> ( ch <-> ( iota x ps ) = B ) )

  proof
    wph
    wps
    wps
    vx
    cio
    #
    vx
    cv
    #
    wceq
    #
    wb
    #
    wch
    @0
    cB
    wceq
    #
    wb
    vx
    cB
    cV
    iota2df.1
    wph
    @1
    cB
    wceq
    #
    wa
    #
    wps
    wch
    @2
    @4
    iota2df.3
    @6
    @1
    cB
    @0
    wph
    @5
    simpr
    eqeq2d
    bibi12d
    wph
    wps
    vx
    weu
    @3
    iota2df.2
    wps
    vx
    iota1
    syl
    iota2df.4
    iota2df.6
    wph
    wch
    @4
    vx
    iota2df.5
    wph
    vx
    @0
    cB
    vx
    @0
    wnfc
    wph
    wps
    vx
    nfiota1
    a1i
    iota2df.6
    nfeqd
    nfbid
    vtocldf
end
