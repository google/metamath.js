include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "cngp.mm"
include "wa.mm"
include "cghm.mm"
include "cnmo.mm"
include "cfv.mm"
include "cr.mm"
include "eqid.mm"
include "isnghm.mm"
include "simplbi.mm"
include "simpld.mm"

theorem nghmrcl1
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S NGHom T ) -> S e. NrmGrp )

  proof
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    @0
    @1
    @2
    wa
    cF
    cS
    cT
    cghm
    co
    wcel
    cF
    cS
    cT
    cnmo
    co
    #
    cfv
    cr
    wcel
    wa
    cS
    cT
    cF
    @3
    @3
    eqid
    isnghm
    simplbi
    simpld
end
