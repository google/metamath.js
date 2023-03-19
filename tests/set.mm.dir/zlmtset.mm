include "wcel.mm"
include "cts.mm"
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
include "tsetid.mm"
include "wne.mm"
include "c9.mm"
include "c5.mm"
include "5re.mm"
include "5lt9.mm"
include "gtneii.mm"
include "tsetndx.mm"
include "scandx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "c6.mm"
include "6re.mm"
include "6lt9.mm"
include "vscandx.mm"
include "3eqtri.mm"
include "syl6reqr.mm"

theorem zlmtset
  let cG: class G
  let cJ: class J
  let cV: class V
  let cW: class W
  assume zlmlem2.1: |- W = ( ZMod ` G )
  assume zlmtset.1: |- J = ( TopSet ` G )


  assert |- ( G e. V -> J = ( TopSet ` W ) )

  proof
    cG
    cV
    wcel
    #
    cW
    cts
    cfv
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
    cts
    cfv
    #
    cJ
    @0
    cW
    @5
    cts
    @4
    cG
    cV
    cW
    zlmlem2.1
    @4
    eqid
    zlmval
    fveq2d
    cJ
    cG
    cts
    cfv
    @2
    cts
    cfv
    @6
    zlmtset.1
    zring
    @1
    cts
    cG
    tsetid
    cnx
    cts
    cfv
    #
    @1
    wne
    c9
    c5
    wne
    c5
    c9
    5re
    5lt9
    gtneii
    @7
    c9
    @1
    c5
    tsetndx
    scandx
    neeq12i
    mpbir
    setsnid
    @4
    @3
    cts
    @2
    tsetid
    @7
    @3
    wne
    c9
    c6
    wne
    c6
    c9
    6re
    6lt9
    gtneii
    @7
    c9
    @3
    c6
    tsetndx
    vscandx
    neeq12i
    mpbir
    setsnid
    3eqtri
    syl6reqr
end
