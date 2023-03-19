include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "wnfc.mm"
include "nfaba1.mm"
include "nfuni.mm"
include "wb.mm"
include "nfnfc1.mm"
include "abidnf.mm"
include "unieqd.mm"
include "nfceqdf.mm"
include "syl.mm"
include "mpbii.mm"

theorem nfunidALT2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume nfunidALT2.1: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x U. A )

  proof
    wph
    vx
    vy
    cv
    cA
    wcel
    #
    vx
    wal
    vy
    cab
    #
    cuni
    #
    wnfc
    #
    vx
    cA
    cuni
    #
    wnfc
    #
    vx
    @1
    @0
    vx
    vy
    nfaba1
    nfuni
    wph
    vx
    cA
    wnfc
    #
    @3
    @5
    wb
    nfunidALT2.1
    @6
    vx
    @2
    @4
    vx
    cA
    nfnfc1
    @6
    @1
    cA
    vx
    vy
    cA
    abidnf
    unieqd
    nfceqdf
    syl
    mpbii
end
