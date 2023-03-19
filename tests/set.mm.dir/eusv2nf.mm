include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "weu.mm"
include "wnfc.mm"
include "wnf.mm"
include "wal.mm"
include "nfeu1.mm"
include "wi.mm"
include "nfe1.mm"
include "nfeu.mm"
include "wa.mm"
include "isseti.mm"
include "19.8a.mm"
include "ancri.mm"
include "eximii.mm"
include "eupick.mm"
include "mpan2.mm"
include "alrimi.mm"
include "nf6.mm"
include "sylibr.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "dfnfc2.mm"
include "mpg.mm"
include "eusvnfb.mm"
include "mpbiran2.mm"
include "eusv2i.mm"
include "sylbir.mm"
include "impbii.mm"

theorem eusv2nf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume eusv2.1: |- A e. _V

  disjoint x y
  disjoint A y
  assert |- ( E! y E. x y = A <-> F/_ x A )

  proof
    vy
    cv
    cA
    wceq
    #
    vx
    wex
    #
    vy
    weu
    #
    vx
    cA
    wnfc
    #
    @2
    @0
    vx
    wnf
    #
    vy
    wal
    #
    @3
    @2
    @4
    vy
    @1
    vy
    nfeu1
    @2
    @1
    @0
    wi
    #
    vx
    wal
    @4
    @2
    @6
    vx
    @1
    vx
    vy
    @0
    vx
    nfe1
    nfeu
    @2
    @1
    @0
    wa
    #
    vy
    wex
    @6
    @0
    @7
    vy
    vy
    cA
    eusv2.1
    isseti
    @0
    @1
    @0
    vx
    19.8a
    ancri
    eximii
    @1
    @0
    vy
    eupick
    mpan2
    alrimi
    @0
    vx
    nf6
    sylibr
    alrimi
    cA
    cvv
    wcel
    #
    @3
    @5
    wb
    vx
    vx
    vy
    cA
    cvv
    dfnfc2
    eusv2.1
    mpg
    sylibr
    @3
    @0
    vx
    wal
    vy
    weu
    #
    @2
    @9
    @3
    @8
    eusv2.1
    vx
    vy
    cA
    eusvnfb
    mpbiran2
    vx
    vy
    cA
    eusv2i
    sylbir
    impbii
end
