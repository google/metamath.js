include "chomf.mm"
include "cfv.mm"
include "cxp.mm"
include "wfn.mm"
include "eqid.mm"
include "homffn.mm"
include "a1i.mm"
include "subcssc.mm"
include "ssc1.mm"

theorem subcss1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cJ: class J
  assume subcss1.1: |- ( ph -> J e. ( Subcat ` C ) )
  assume subcss1.2: |- ( ph -> J Fn ( S X. S ) )
  assume subcss1.b: |- B = ( Base ` C )


  assert |- ( ph -> S C_ B )

  proof
    wph
    cS
    cB
    cJ
    cC
    chomf
    cfv
    #
    subcss1.2
    @0
    cB
    cB
    cxp
    wfn
    wph
    cB
    cC
    @0
    @0
    eqid
    #
    subcss1.b
    homffn
    a1i
    wph
    cC
    @0
    cJ
    subcss1.1
    @1
    subcssc
    ssc1
end
