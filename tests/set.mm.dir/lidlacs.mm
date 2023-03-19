include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clss.mm"
include "cacs.mm"
include "clidl.mm"
include "lidlval.mm"
include "eqtri.mm"
include "clmod.mm"
include "rlmlmod.mm"
include "cbs.mm"
include "rlmbas.mm"
include "eqid.mm"
include "lssacs.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem lidlacs
  let cB: class B
  let cI: class I
  let cW: class W
  assume lidlacs.b: |- B = ( Base ` W )
  assume lidlacs.i: |- I = ( LIdeal ` W )


  assert |- ( W e. Ring -> I e. ( ACS ` B ) )

  proof
    cW
    crg
    wcel
    #
    cI
    cW
    crglmod
    cfv
    #
    clss
    cfv
    #
    cB
    cacs
    cfv
    #
    cI
    cW
    clidl
    cfv
    @2
    lidlacs.i
    cW
    lidlval
    eqtri
    @0
    @1
    clmod
    wcel
    @2
    @3
    wcel
    cW
    rlmlmod
    cB
    @2
    @1
    cB
    cW
    cbs
    cfv
    @1
    cbs
    cfv
    lidlacs.b
    cW
    rlmbas
    eqtri
    @2
    eqid
    lssacs
    syl
    syl5eqel
end
