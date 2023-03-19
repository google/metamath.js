include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "wnfc.mm"
include "abidnf.mm"
include "unieqd.mm"
include "nfaba1.mm"
include "nfuni.mm"
include "nfded.mm"

theorem nfunidALT
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume nfunidALT.1: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x U. A )

  proof
    wph
    vx
    cA
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
    cA
    cuni
    nfunidALT.1
    vx
    cA
    wnfc
    @1
    cA
    vx
    vy
    cA
    abidnf
    unieqd
    vx
    @1
    @0
    vx
    vy
    nfaba1
    nfuni
    nfded
end
