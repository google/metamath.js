include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "cress.mm"
include "eqid.mm"
include "resghm.mm"
include "ghmrn.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem ghmima
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F


  assert |- ( ( F e. ( S GrpHom T ) /\ U e. ( SubGrp ` S ) ) -> ( F " U ) e. ( SubGrp ` T ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    cU
    cS
    csubg
    cfv
    wcel
    wa
    #
    cF
    cU
    cima
    cF
    cU
    cres
    #
    crn
    #
    cT
    csubg
    cfv
    #
    cF
    cU
    df-ima
    @0
    @1
    cS
    cU
    cress
    co
    #
    cT
    cghm
    co
    wcel
    @2
    @3
    wcel
    cS
    cT
    @4
    cF
    cU
    @4
    eqid
    resghm
    @4
    cT
    @1
    ghmrn
    syl
    syl5eqel
end
