include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clss.mm"
include "clmod.mm"
include "rlmlmod.mm"
include "cbs.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "eqid.mm"
include "lss1.mm"
include "syl.mm"
include "clidl.mm"
include "lidlval.mm"
include "syl6eleqr.mm"

theorem lidl1
  let cB: class B
  let cR: class R
  let cU: class U
  assume lidl0.u: |- U = ( LIdeal ` R )
  assume lidl1.b: |- B = ( Base ` R )


  assert |- ( R e. Ring -> B e. U )

  proof
    cR
    crg
    wcel
    #
    cB
    cR
    crglmod
    cfv
    #
    clss
    cfv
    #
    cU
    @0
    @1
    clmod
    wcel
    cB
    @2
    wcel
    cR
    rlmlmod
    @2
    cB
    @1
    cB
    cR
    cbs
    cfv
    @1
    cbs
    cfv
    lidl1.b
    cR
    rlmbas
    eqtri
    @2
    eqid
    lss1
    syl
    cU
    cR
    clidl
    cfv
    @2
    lidl0.u
    cR
    lidlval
    eqtri
    syl6eleqr
end
