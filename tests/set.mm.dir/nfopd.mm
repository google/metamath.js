include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "cop.mm"
include "wnfc.mm"
include "nfaba1.mm"
include "nfop.mm"
include "wb.mm"
include "wa.mm"
include "nfnfc1.mm"
include "nfan.mm"
include "wceq.mm"
include "abidnf.mm"
include "adantr.mm"
include "adantl.mm"
include "opeq12d.mm"
include "nfceqdf.mm"
include "syl2anc.mm"
include "mpbii.mm"

theorem nfopd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfopd.2: |- ( ph -> F/_ x A )
  assume nfopd.3: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x <. A , B >. )

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
    cop
    #
    wnfc
    #
    vx
    cA
    cB
    cop
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
    nfop
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
    nfopd.2
    nfopd.3
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
    cA
    nfnfc1
    vx
    cB
    nfnfc1
    nfan
    @11
    @2
    cA
    @4
    cB
    @9
    @2
    cA
    wceq
    @10
    vx
    vz
    cA
    abidnf
    adantr
    @10
    @4
    cB
    wceq
    @9
    vx
    vz
    cB
    abidnf
    adantl
    opeq12d
    nfceqdf
    syl2anc
    mpbii
end
