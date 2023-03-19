include "crn.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "ghmrn.mm"
include "wss.mm"
include "wb.mm"
include "ssid.mm"
include "resghm2b.mm"
include "mpan2.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem ghmghmrn
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  assume ghmghmrn.u: |- U = ( T |`s ran F )


  assert |- ( F e. ( S GrpHom T ) -> F e. ( S GrpHom U ) )

  proof
    cF
    crn
    #
    cT
    csubg
    cfv
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
    cU
    cghm
    co
    wcel
    #
    cS
    cT
    cF
    ghmrn
    @1
    @2
    @3
    @1
    @0
    @0
    wss
    @2
    @3
    wb
    @0
    ssid
    cS
    cT
    cU
    cF
    @0
    ghmghmrn.u
    resghm2b
    mpan2
    biimpd
    mpcom
end
