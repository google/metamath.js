include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "clno.mm"
include "co.mm"
include "cnmoo.mm"
include "cfv.mm"
include "cr.mm"
include "eqid.mm"
include "0lno.mm"
include "cc0.mm"
include "nmoo0.mm"
include "0re.mm"
include "syl6eqel.mm"
include "isblo2.mm"
include "mpbir2and.mm"

theorem 0blo
  let cB: class B
  let cU: class U
  let cW: class W
  let cZ: class Z
  assume 0blo.0: |- Z = ( U 0op W )
  assume 0blo.7: |- B = ( U BLnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z e. B )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    #
    cZ
    cB
    wcel
    cZ
    cU
    cW
    clno
    co
    #
    wcel
    cZ
    cU
    cW
    cnmoo
    co
    #
    cfv
    #
    cr
    wcel
    cU
    @1
    cW
    cZ
    0blo.0
    @1
    eqid
    #
    0lno
    @0
    @3
    cc0
    cr
    cU
    @2
    cW
    cZ
    @2
    eqid
    #
    0blo.0
    nmoo0
    0re
    syl6eqel
    cB
    cZ
    cU
    @1
    @2
    cW
    @5
    @4
    0blo.7
    isblo2
    mpbir2and
end
