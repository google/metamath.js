include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cnmo.mm"
include "cfv.mm"
include "cr.mm"
include "cngp.mm"
include "wa.mm"
include "eqid.mm"
include "isnghm.mm"
include "simprbi.mm"
include "simpld.mm"

theorem nghmghm
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S NGHom T ) -> F e. ( S GrpHom T ) )

  proof
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cF
    cS
    cT
    cnmo
    co
    #
    cfv
    cr
    wcel
    #
    @0
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    wa
    @1
    @3
    wa
    cS
    cT
    cF
    @2
    @2
    eqid
    isnghm
    simprbi
    simpld
end
