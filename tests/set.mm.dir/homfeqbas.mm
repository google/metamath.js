include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cdm.mm"
include "chomf.mm"
include "dmeqd.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "homffn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "dmxpid.mm"

theorem homfeqbas
  let wph: wff ph
  let cC: class C
  let cD: class D
  assume homfeqbas.1: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )


  assert |- ( ph -> ( Base ` C ) = ( Base ` D ) )

  proof
    wph
    cC
    cbs
    cfv
    #
    @0
    cxp
    #
    cdm
    cD
    cbs
    cfv
    #
    @2
    cxp
    #
    cdm
    @0
    @2
    wph
    @1
    @3
    wph
    cC
    chomf
    cfv
    #
    cdm
    #
    cD
    chomf
    cfv
    #
    cdm
    #
    @1
    @3
    wph
    @4
    @6
    homfeqbas.1
    dmeqd
    @4
    @1
    wfn
    @5
    @1
    wceq
    @0
    cC
    @4
    @4
    eqid
    @0
    eqid
    homffn
    @1
    @4
    fndm
    ax-mp
    @6
    @3
    wfn
    @7
    @3
    wceq
    @2
    cD
    @6
    @6
    eqid
    @2
    eqid
    homffn
    @3
    @6
    fndm
    ax-mp
    3eqtr3g
    dmeqd
    @0
    dmxpid
    @2
    dmxpid
    3eqtr3g
end
