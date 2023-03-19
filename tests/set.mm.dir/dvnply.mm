include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cn0.mm"
include "cdvn.mm"
include "co.mm"
include "plyssc.mm"
include "sseli.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "subrgid.mm"
include "ax-mp.mm"
include "dvnply2.mm"
include "mp3an1.mm"
include "sylan.mm"

theorem dvnply
  let cS: class S
  let cF: class F
  let cN: class N
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( F e. ( Poly ` S ) /\ N e. NN0 ) -> ( ( CC Dn F ) ` N ) e. ( Poly ` CC ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cF
    cc
    cply
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cc
    cF
    cdvn
    co
    cfv
    @1
    wcel
    #
    @0
    @1
    cF
    cS
    plyssc
    sseli
    cc
    ccnfld
    csubrg
    cfv
    wcel
    #
    @2
    @3
    @4
    ccnfld
    crg
    wcel
    @5
    cnring
    cc
    ccnfld
    cnfldbas
    subrgid
    ax-mp
    cc
    cF
    cN
    dvnply2
    mp3an1
    sylan
end
