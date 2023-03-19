include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "cima.mm"
include "wnfc.mm"
include "nfaba1.mm"
include "nfima.mm"
include "wb.mm"
include "wa.mm"
include "nfnfc1.mm"
include "nfan.mm"
include "abidnf.mm"
include "imaeq1d.mm"
include "imaeq2d.mm"
include "sylan9eq.mm"
include "nfceqdf.mm"
include "syl2anc.mm"
include "mpbii.mm"

theorem nfimad
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfimad.2: |- ( ph -> F/_ x A )
  assume nfimad.3: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x ( A " B ) )

  proof
    wph
    vx
    vz
    cv
    #
    cA
    wcel
    #
    vx
    wal
    vz
    cab
    #
    @0
    cB
    wcel
    #
    vx
    wal
    vz
    cab
    #
    cima
    #
    wnfc
    #
    vx
    cA
    cB
    cima
    #
    wnfc
    #
    vx
    @2
    @4
    @1
    vx
    vz
    nfaba1
    @3
    vx
    vz
    nfaba1
    nfima
    wph
    vx
    cA
    wnfc
    #
    vx
    cB
    wnfc
    #
    @6
    @8
    wb
    nfimad.2
    nfimad.3
    @9
    @10
    wa
    vx
    @5
    @7
    @9
    @10
    vx
    vx
    cA
    nfnfc1
    vx
    cB
    nfnfc1
    nfan
    @9
    @10
    @5
    cA
    @4
    cima
    @7
    @9
    @2
    cA
    @4
    vx
    vz
    cA
    abidnf
    imaeq1d
    @10
    @4
    cB
    cA
    vx
    vz
    cB
    abidnf
    imaeq2d
    sylan9eq
    nfceqdf
    syl2anc
    mpbii
end
