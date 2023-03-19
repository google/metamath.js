include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
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
include "ndxid.mm"
include "c5.mm"
include "cr.mm"
include "ndxarg.mm"
include "nnrei.mm"
include "eqeltri.mm"
include "clt.mm"
include "eqbrtri.mm"
include "ltneii.mm"
include "scandx.mm"
include "neeqtrri.mm"
include "setsnid.mm"
include "c6.mm"
include "wbr.mm"
include "5lt6.mm"
include "5re.mm"
include "6re.mm"
include "lttri.mm"
include "mp2an.mm"
include "vscandx.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "czlm.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem zlmlem
  let cE: class E
  let cG: class G
  let cN: class N
  let cW: class W
  assume zlmbas.w: |- W = ( ZMod ` G )
  assume zlmlem.2: |- E = Slot N
  assume zlmlem.3: |- N e. NN
  assume zlmlem.4: |- N < 5


  assert |- ( E ` G ) = ( E ` W )

  proof
    cG
    cvv
    wcel
    #
    cG
    cE
    cfv
    #
    cW
    cE
    cfv
    #
    wceq
    @0
    @2
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
    cE
    cfv
    #
    @1
    @0
    cW
    @7
    cE
    @6
    cG
    cvv
    cW
    zlmbas.w
    @6
    eqid
    zlmval
    fveq2d
    @1
    @4
    cE
    cfv
    @8
    zring
    @3
    cE
    cG
    cE
    cN
    zlmlem.2
    zlmlem.3
    ndxid
    #
    cnx
    cE
    cfv
    #
    c5
    @3
    @10
    c5
    @10
    cN
    cr
    cE
    cN
    zlmlem.2
    zlmlem.3
    ndxarg
    #
    cN
    zlmlem.3
    nnrei
    eqeltri
    #
    @10
    cN
    c5
    clt
    @11
    zlmlem.4
    eqbrtri
    #
    ltneii
    scandx
    neeqtrri
    setsnid
    @6
    @5
    cE
    @4
    @9
    @10
    c6
    @5
    @10
    c6
    @12
    @10
    c5
    clt
    wbr
    c5
    c6
    clt
    wbr
    @10
    c6
    clt
    wbr
    @13
    5lt6
    @10
    c5
    c6
    @12
    5re
    6re
    lttri
    mp2an
    ltneii
    vscandx
    neeqtrri
    setsnid
    eqtri
    syl6reqr
    @0
    wn
    #
    c0
    c0
    cE
    cfv
    @1
    @2
    cE
    cN
    zlmlem.2
    str0
    cG
    cE
    fvprc
    @14
    cW
    c0
    cE
    @14
    cW
    cG
    czlm
    cfv
    c0
    zlmbas.w
    cG
    czlm
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
