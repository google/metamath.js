include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cab.mm"
include "cres.mm"
include "wfun.mm"
include "wrel.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "relres.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "brres.mm"
include "abid.mm"
include "tz6.12-1.mm"
include "sylan2b.mm"
include "eqcomd.mm"
include "sylbi.mm"
include "mpg.mm"
include "ax-gen.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nfres.mm"
include "nfeu1.mm"
include "nfab.mm"
include "dffun3f.mm"
include "mpbir2an.mm"

theorem setrec2lem2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let vk: setvar k

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k x
  assert |- Fun ( F |` { x | E! y x F y } )

  proof
    cF
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    weu
    #
    vx
    cab
    #
    cres
    #
    wfun
    @5
    wrel
    @0
    @1
    @5
    wbr
    #
    @1
    vz
    cv
    #
    wceq
    #
    wi
    #
    vy
    wal
    #
    vz
    wex
    #
    vx
    wal
    cF
    @4
    relres
    @11
    vx
    @6
    @1
    @0
    cF
    cfv
    #
    wceq
    #
    wi
    #
    @11
    vy
    @10
    @14
    vy
    wal
    vz
    @12
    @0
    cF
    fvex
    @7
    @12
    wceq
    #
    @9
    @14
    vy
    @15
    @8
    @13
    @6
    @7
    @12
    @1
    eqeq2
    imbi2d
    albidv
    spcev
    @6
    @2
    @0
    @4
    wcel
    #
    wa
    #
    @13
    @0
    @1
    cF
    @4
    vy
    vex
    brres
    @17
    @12
    @1
    @16
    @2
    @3
    @12
    @1
    wceq
    @3
    vx
    abid
    vy
    @0
    cF
    tz6.12-1
    sylan2b
    eqcomd
    sylbi
    mpg
    ax-gen
    vx
    vy
    vz
    @5
    vx
    cF
    @4
    vx
    cF
    nfcv
    @3
    vx
    nfab1
    nfres
    vy
    cF
    @4
    vy
    cF
    nfcv
    @3
    vy
    vx
    @2
    vy
    nfeu1
    nfab
    nfres
    vz
    @5
    nfcv
    dffun3f
    mpbir2an
end
