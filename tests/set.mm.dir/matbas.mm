include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
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
include "baseid.mm"
include "c1.mm"
include "basendx.mm"
include "c3.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "mulrndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"
include "setsnid.mm"
include "syl6reqr.mm"

theorem matbas
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cV: class V
  assume matbas.a: |- A = ( N Mat R )
  assume matbas.g: |- G = ( R freeLMod ( N X. N ) )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( Base ` G ) = ( Base ` A ) )

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
    cbs
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
    cbs
    cfv
    cG
    cbs
    cfv
    @0
    cA
    @3
    cbs
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
    cbs
    cG
    baseid
    cnx
    cbs
    cfv
    c1
    @1
    basendx
    c1
    c3
    @1
    c1
    c3
    1re
    1lt3
    ltneii
    mulrndx
    neeqtrri
    eqnetri
    setsnid
    syl6reqr
end
