include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "ax6e.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfeqf.mm"
include "pm3.21.mm"
include "spimed.mm"
include "eximd.mm"
include "mpi.mm"
include "ex.mm"
include "nfae.mm"
include "equvini.mm"
include "equtrr.mm"
include "anim1d.mm"
include "aleximi.mm"
include "syl5.mm"
include "pm2.61d2.mm"

theorem 2ax6elem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( -. A. w w = z -> E. z E. w ( z = x /\ w = y ) )

  proof
    vw
    vz
    weq
    vw
    wal
    wn
    #
    vw
    vx
    weq
    #
    vw
    wal
    #
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    @0
    @2
    wn
    #
    @7
    @0
    @8
    wa
    #
    @3
    vz
    wex
    @7
    vz
    vx
    ax6e
    @9
    @3
    @6
    vz
    @0
    @8
    vz
    vw
    vz
    vz
    nfnae
    vw
    vx
    vz
    nfnae
    nfan
    @3
    @5
    @9
    vw
    vy
    vz
    vx
    vw
    nfeqf
    @4
    @3
    pm3.21
    spimed
    eximd
    mpi
    ex
    @2
    vz
    vy
    weq
    #
    vz
    wex
    @7
    vz
    vy
    ax6e
    @2
    @10
    @6
    vz
    vw
    vx
    vz
    nfae
    @10
    vz
    vw
    weq
    #
    @4
    wa
    #
    vw
    wex
    @2
    @6
    vz
    vy
    vw
    equvini
    @1
    @12
    @5
    vw
    @1
    @11
    @3
    @4
    vw
    vx
    vz
    equtrr
    anim1d
    aleximi
    syl5
    eximd
    mpi
    pm2.61d2
end
