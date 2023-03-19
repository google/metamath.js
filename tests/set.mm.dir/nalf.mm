include "wfal.mm"
include "wal.mm"
include "wn.mm"
include "alnof.mm"
include "falim.mm"
include "sps.mm"
include "mt2.mm"

theorem nalf
  let vx: setvar x


  assert |- -. A. x F.

  proof
    wfal
    vx
    wal
    wfal
    wn
    vx
    wal
    #
    vx
    alnof
    wfal
    @0
    wn
    #
    vx
    @1
    falim
    sps
    mt2
end
