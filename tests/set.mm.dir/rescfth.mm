include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cfth.mm"
include "co.mm"
include "cresc.mm"
include "oveq2i.mm"
include "fthres2.mm"
include "syl5eqss.mm"
include "cful.mm"
include "cin.mm"
include "inss2.mm"
include "ccat.mm"
include "id.mm"
include "subccat.mm"
include "idffth.mm"
include "syl.mm"
include "sseldi.mm"
include "sseldd.mm"

theorem rescfth
  let cC: class C
  let cD: class D
  let cI: class I
  let cJ: class J
  assume rescfth.d: |- D = ( C |`cat J )
  assume rescfth.i: |- I = ( idFunc ` D )


  assert |- ( J e. ( Subcat ` C ) -> I e. ( D Faith C ) )

  proof
    cJ
    cC
    csubc
    cfv
    wcel
    #
    cD
    cD
    cfth
    co
    #
    cD
    cC
    cfth
    co
    #
    cI
    @0
    @1
    cD
    cC
    cJ
    cresc
    co
    #
    cfth
    co
    @2
    cD
    @3
    cD
    cfth
    rescfth.d
    oveq2i
    cD
    cC
    cJ
    fthres2
    syl5eqss
    @0
    cD
    cD
    cful
    co
    #
    @1
    cin
    #
    @1
    cI
    @4
    @1
    inss2
    @0
    cD
    ccat
    wcel
    cI
    @5
    wcel
    @0
    cC
    cD
    cJ
    rescfth.d
    @0
    id
    subccat
    cD
    cI
    rescfth.i
    idffth
    syl
    sseldi
    sseldd
end
