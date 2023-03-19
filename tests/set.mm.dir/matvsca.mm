include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "cnx.mm"
include "cmulr.mm"
include "cotp.mm"
include "cmmul.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "eqid.mm"
include "matval.mm"
include "fveq2d.mm"
include "vscaid.mm"
include "c6.mm"
include "vscandx.mm"
include "c3.mm"
include "3re.mm"
include "3lt6.mm"
include "gtneii.mm"
include "mulrndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"
include "setsnid.mm"
include "syl6reqr.mm"

theorem matvsca
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cV: class V
  assume matbas.a: |- A = ( N Mat R )
  assume matbas.g: |- G = ( R freeLMod ( N X. N ) )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( .s ` G ) = ( .s ` A ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    #
    cA
    cvsca
    cfv
    cG
    cnx
    cmulr
    cfv
    #
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    cop
    csts
    co
    #
    cvsca
    cfv
    cG
    cvsca
    cfv
    @0
    cA
    @3
    cvsca
    cA
    cR
    @2
    cG
    cN
    cV
    matbas.a
    matbas.g
    @2
    eqid
    matval
    fveq2d
    @2
    @1
    cvsca
    cG
    vscaid
    cnx
    cvsca
    cfv
    c6
    @1
    vscandx
    c6
    c3
    @1
    c3
    c6
    3re
    3lt6
    gtneii
    mulrndx
    neeqtrri
    eqnetri
    setsnid
    syl6reqr
end
