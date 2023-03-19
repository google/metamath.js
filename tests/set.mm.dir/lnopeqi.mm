include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "chod.mm"
include "cc0.mm"
include "ch0o.mm"
include "wcel.mm"
include "cmin.mm"
include "cc.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "hicl.mm"
include "mpancom.mm"
include "subeq0ad.mm"
include "cmv.mm"
include "wf.mm"
include "hodval.mm"
include "mp3an12.mm"
include "oveq1d.mm"
include "id.mm"
include "his2sub.mm"
include "syl3anc.mm"
include "eqtr2d.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "ralbiia.mm"
include "lnophdi.mm"
include "lnopeq0i.mm"
include "hosubeq0i.mm"
include "3bitri.mm"

theorem lnopeqi
  let vx: setvar x
  let cT: class T
  let cU: class U
  assume lnopeq.1: |- T e. LinOp
  assume lnopeq.2: |- U e. LinOp

  disjoint T x
  disjoint U x
  assert |- ( A. x e. ~H ( ( T ` x ) .ih x ) = ( ( U ` x ) .ih x ) <-> T = U )

  proof
    vx
    cv
    #
    cT
    cfv
    #
    @0
    csp
    co
    #
    @0
    cU
    cfv
    #
    @0
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    @0
    cT
    cU
    chod
    co
    #
    cfv
    #
    @0
    csp
    co
    #
    cc0
    wceq
    #
    vx
    chil
    wral
    @6
    ch0o
    wceq
    cT
    cU
    wceq
    @5
    @9
    vx
    chil
    @0
    chil
    wcel
    #
    @2
    @4
    cmin
    co
    #
    cc0
    wceq
    @5
    @9
    @10
    @2
    @4
    @1
    chil
    wcel
    #
    @10
    @2
    cc
    wcel
    chil
    chil
    @0
    cT
    cT
    lnopeq.1
    lnopfi
    #
    ffvelrni
    #
    @1
    @0
    hicl
    mpancom
    @3
    chil
    wcel
    #
    @10
    @4
    cc
    wcel
    chil
    chil
    @0
    cU
    cU
    lnopeq.2
    lnopfi
    #
    ffvelrni
    #
    @3
    @0
    hicl
    mpancom
    subeq0ad
    @10
    @11
    @8
    cc0
    @10
    @8
    @1
    @3
    cmv
    co
    #
    @0
    csp
    co
    #
    @11
    @10
    @7
    @18
    @0
    csp
    chil
    chil
    cT
    wf
    chil
    chil
    cU
    wf
    @10
    @7
    @18
    wceq
    @13
    @16
    @0
    cT
    cU
    hodval
    mp3an12
    oveq1d
    @10
    @12
    @15
    @10
    @19
    @11
    wceq
    @14
    @17
    @10
    id
    @1
    @3
    @0
    his2sub
    syl3anc
    eqtr2d
    eqeq1d
    bitr3d
    ralbiia
    vx
    @6
    cT
    cU
    lnopeq.1
    lnopeq.2
    lnophdi
    lnopeq0i
    cT
    cU
    @13
    @16
    hosubeq0i
    3bitri
end
