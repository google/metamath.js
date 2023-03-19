include "cz.mm"
include "wcel.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cli.mm"
include "eqid.mm"
include "ser0f.mm"
include "cc.mm"
include "wbr.mm"
include "0cn.mm"
include "ssid.mm"
include "fvex.mm"
include "climconst2.mm"
include "mpan.mm"
include "eqbrtrd.mm"

theorem serclim0
  let cM: class M


  assert |- ( M e. ZZ -> seq M ( + , ( ( ZZ>= ` M ) X. { 0 } ) ) ~~> 0 )

  proof
    cM
    cz
    wcel
    #
    caddc
    cM
    cuz
    cfv
    #
    cc0
    csn
    cxp
    #
    cM
    cseq
    @2
    cc0
    cli
    cM
    @1
    @1
    eqid
    ser0f
    cc0
    cc
    wcel
    @0
    @2
    cc0
    cli
    wbr
    0cn
    cc0
    cM
    @1
    @1
    ssid
    cM
    cuz
    fvex
    climconst2
    mpan
    eqbrtrd
end
