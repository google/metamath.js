include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "cfv.mm"
include "wnfc.mm"
include "nfaba1.mm"
include "nffv.mm"
include "wb.mm"
include "wa.mm"
include "nfnfc1.mm"
include "nfan.mm"
include "wceq.mm"
include "abidnf.mm"
include "adantr.mm"
include "adantl.mm"
include "fveq12d.mm"
include "nfceqdf.mm"
include "syl2anc.mm"
include "mpbii.mm"

theorem nffvd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vz: setvar z
  assume nffvd.2: |- ( ph -> F/_ x F )
  assume nffvd.3: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x ( F ` A ) )

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
    cF
    wcel
    #
    vx
    wal
    vz
    cab
    #
    cfv
    #
    wnfc
    #
    vx
    cA
    cF
    cfv
    #
    wnfc
    #
    vx
    @2
    @4
    @3
    vx
    vz
    nfaba1
    @1
    vx
    vz
    nfaba1
    nffv
    wph
    vx
    cF
    wnfc
    #
    vx
    cA
    wnfc
    #
    @6
    @8
    wb
    nffvd.2
    nffvd.3
    @9
    @10
    wa
    #
    vx
    @5
    @7
    @9
    @10
    vx
    vx
    cF
    nfnfc1
    vx
    cA
    nfnfc1
    nfan
    @11
    @2
    cA
    @4
    cF
    @9
    @4
    cF
    wceq
    @10
    vx
    vz
    cF
    abidnf
    adantr
    @10
    @2
    cA
    wceq
    @9
    vx
    vz
    cA
    abidnf
    adantl
    fveq12d
    nfceqdf
    syl2anc
    mpbii
end
