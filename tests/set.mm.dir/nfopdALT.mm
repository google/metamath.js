include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "cop.mm"
include "wnfc.mm"
include "wa.mm"
include "wceq.mm"
include "abidnf.mm"
include "adantr.mm"
include "adantl.mm"
include "opeq12d.mm"
include "nfaba1.mm"
include "nfop.mm"
include "nfded2.mm"

theorem nfopdALT
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfopdALT.1: |- ( ph -> F/_ x A )
  assume nfopdALT.2: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x <. A , B >. )

  proof
    wph
    vx
    cA
    cB
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
    cA
    cB
    cop
    nfopdALT.1
    nfopdALT.2
    vx
    cA
    wnfc
    #
    vx
    cB
    wnfc
    #
    wa
    @2
    cA
    @4
    cB
    @5
    @2
    cA
    wceq
    @6
    vx
    vz
    cA
    abidnf
    adantr
    @6
    @4
    cB
    wceq
    @5
    vx
    vz
    cB
    abidnf
    adantl
    opeq12d
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
    nfded2
end
