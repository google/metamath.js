include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
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
include "scaid.mm"
include "wne.mm"
include "c5.mm"
include "c3.mm"
include "3re.mm"
include "3lt5.mm"
include "gtneii.mm"
include "scandx.mm"
include "mulrndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "syl6reqr.mm"

theorem matsca
  let cA: class A
  let cR: class R
  let cG: class G
  let cN: class N
  let cV: class V
  assume matbas.a: |- A = ( N Mat R )
  assume matbas.g: |- G = ( R freeLMod ( N X. N ) )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( Scalar ` G ) = ( Scalar ` A ) )

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
    csca
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
    csca
    cfv
    cG
    csca
    cfv
    @0
    cA
    @3
    csca
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
    csca
    cG
    scaid
    cnx
    csca
    cfv
    #
    @1
    wne
    c5
    c3
    wne
    c3
    c5
    3re
    3lt5
    gtneii
    @4
    c5
    @1
    c3
    scandx
    mulrndx
    neeq12i
    mpbir
    setsnid
    syl6reqr
end
