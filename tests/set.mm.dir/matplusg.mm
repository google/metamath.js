include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
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
include "plusgid.mm"
include "c2.mm"
include "plusgndx.mm"
include "c3.mm"
include "2re.mm"
include "2lt3.mm"
include "ltneii.mm"
include "mulrndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"
include "setsnid.mm"
include "syl6reqr.mm"

theorem matplusg
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cV: class V
  assume matbas.a: |- A = ( N Mat R )
  assume matbas.g: |- G = ( R freeLMod ( N X. N ) )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( +g ` G ) = ( +g ` A ) )

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
    cplusg
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
    cplusg
    cfv
    cG
    cplusg
    cfv
    @0
    cA
    @3
    cplusg
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
    cplusg
    cG
    plusgid
    cnx
    cplusg
    cfv
    c2
    @1
    plusgndx
    c2
    c3
    @1
    c2
    c3
    2re
    2lt3
    ltneii
    mulrndx
    neeqtrri
    eqnetri
    setsnid
    syl6reqr
end
