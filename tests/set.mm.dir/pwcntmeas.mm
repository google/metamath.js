include "wcel.mm"
include "cpw.mm"
include "csiga.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "chash.mm"
include "cres.mm"
include "cmeas.mm"
include "pwsiga.mm"
include "elrnsiga.mm"
include "cntmeas.mm"
include "3syl.mm"

theorem pwcntmeas
  let cO: class O
  let cV: class V


  assert |- ( O e. V -> ( # |` ~P O ) e. ( measures ` ~P O ) )

  proof
    cO
    cV
    wcel
    cO
    cpw
    #
    cO
    csiga
    cfv
    wcel
    @0
    csiga
    crn
    cuni
    wcel
    chash
    @0
    cres
    @0
    cmeas
    cfv
    wcel
    cO
    cV
    pwsiga
    @0
    cO
    elrnsiga
    @0
    cntmeas
    3syl
end
