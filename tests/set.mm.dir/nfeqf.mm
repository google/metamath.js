include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "nfna1.mm"
include "nfan.mm"
include "wex.mm"
include "equviniva.mm"
include "dveeq1.mm"
include "imp.mm"
include "equtr2.mm"
include "alanimi.mm"
include "syl2an.mm"
include "an4s.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "nf5d.mm"

theorem nfeqf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y )

  proof
    vz
    vx
    weq
    #
    vz
    wal
    wn
    #
    vz
    vy
    weq
    #
    vz
    wal
    wn
    #
    wa
    #
    vx
    vy
    weq
    #
    vz
    @1
    @3
    vz
    @0
    vz
    nfna1
    @2
    vz
    nfna1
    nfan
    @5
    vx
    vw
    weq
    #
    vy
    vw
    weq
    #
    wa
    #
    vw
    wex
    @4
    @5
    vz
    wal
    #
    vx
    vy
    vw
    equviniva
    @4
    @8
    @9
    vw
    @4
    @8
    @9
    @1
    @6
    @3
    @7
    @9
    @1
    @6
    wa
    @6
    vz
    wal
    #
    @7
    vz
    wal
    #
    @9
    @3
    @7
    wa
    @1
    @6
    @10
    vz
    vx
    vw
    dveeq1
    imp
    @3
    @7
    @11
    vz
    vy
    vw
    dveeq1
    imp
    @6
    @7
    @5
    vz
    vx
    vy
    vw
    equtr2
    alanimi
    syl2an
    an4s
    ex
    exlimdv
    syl5
    nf5d
end
