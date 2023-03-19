include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cnx.mm"
include "csca.mm"
include "zring.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvsca.mm"
include "cmg.mm"
include "eqid.mm"
include "zlmval.mm"
include "fveq2d.mm"
include "dsid.mm"
include "wne.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "c5.mm"
include "5re.mm"
include "1nn.mm"
include "2nn0.mm"
include "5nn0.mm"
include "5lt10.mm"
include "declti.mm"
include "gtneii.mm"
include "dsndx.mm"
include "scandx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "c6.mm"
include "6re.mm"
include "6nn0.mm"
include "6lt10.mm"
include "vscandx.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "syl6reqr.mm"

theorem zlmds
  let cD: class D
  let cG: class G
  let cV: class V
  let cW: class W
  assume zlmlem2.1: |- W = ( ZMod ` G )
  assume zlmds.1: |- D = ( dist ` G )


  assert |- ( G e. V -> D = ( dist ` W ) )

  proof
    cG
    cV
    wcel
    #
    cW
    cds
    cfv
    #
    cG
    cds
    cfv
    #
    cD
    @0
    @1
    cG
    cnx
    csca
    cfv
    #
    zring
    cop
    csts
    co
    #
    cnx
    cvsca
    cfv
    #
    cG
    cmg
    cfv
    #
    cop
    csts
    co
    #
    cds
    cfv
    #
    @2
    @0
    cW
    @7
    cds
    @6
    cG
    cV
    cW
    zlmlem2.1
    @6
    eqid
    zlmval
    fveq2d
    @2
    @4
    cds
    cfv
    @8
    zring
    @3
    cds
    cG
    dsid
    cnx
    cds
    cfv
    #
    @3
    wne
    c1
    c2
    cdc
    #
    c5
    wne
    c5
    @10
    5re
    c1
    c2
    c5
    1nn
    2nn0
    5nn0
    5lt10
    declti
    gtneii
    @9
    @10
    @3
    c5
    dsndx
    scandx
    neeq12i
    mpbir
    setsnid
    @6
    @5
    cds
    @4
    dsid
    @9
    @5
    wne
    @10
    c6
    wne
    c6
    @10
    6re
    c1
    c2
    c6
    1nn
    2nn0
    6nn0
    6lt10
    declti
    gtneii
    @9
    @10
    @5
    c6
    dsndx
    vscandx
    neeq12i
    mpbir
    setsnid
    eqtri
    syl6eqr
    zlmds.1
    syl6reqr
end
