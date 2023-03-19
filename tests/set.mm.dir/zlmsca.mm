include "wcel.mm"
include "cnx.mm"
include "csca.mm"
include "cfv.mm"
include "zring.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvsca.mm"
include "cmg.mm"
include "scaid.mm"
include "wne.mm"
include "c5.mm"
include "c6.mm"
include "5re.mm"
include "5lt6.mm"
include "ltneii.mm"
include "scandx.mm"
include "vscandx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "crg.mm"
include "wceq.mm"
include "zringring.mm"
include "setsid.mm"
include "mpan2.mm"
include "eqid.mm"
include "zlmval.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"

theorem zlmsca
  let cG: class G
  let cV: class V
  let cW: class W
  assume zlmbas.w: |- W = ( ZMod ` G )


  assert |- ( G e. V -> ZZring = ( Scalar ` W ) )

  proof
    cG
    cV
    wcel
    #
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
    csca
    cfv
    #
    @2
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
    csca
    cfv
    zring
    cW
    csca
    cfv
    @5
    @4
    csca
    @2
    scaid
    @1
    @4
    wne
    c5
    c6
    wne
    c5
    c6
    5re
    5lt6
    ltneii
    @1
    c5
    @4
    c6
    scandx
    vscandx
    neeq12i
    mpbir
    setsnid
    @0
    zring
    crg
    wcel
    zring
    @3
    wceq
    zringring
    cV
    zring
    csca
    crg
    cG
    scaid
    setsid
    mpan2
    @0
    cW
    @6
    csca
    @5
    cG
    cV
    cW
    zlmbas.w
    @5
    eqid
    zlmval
    fveq2d
    3eqtr4a
end
