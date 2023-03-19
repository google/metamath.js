include "ctx.mm"
include "co.mm"
include "cuni.mm"
include "crn.mm"
include "wceq.mm"
include "csigagen.mm"
include "cfv.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "cr.mm"
include "cxp.mm"
include "dya2iocucvr.mm"
include "cioo.mm"
include "ctg.mm"
include "ctop.mm"
include "retop.mm"
include "eqeltri.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "txunii.mm"
include "eqtr2i.mm"
include "cv.mm"
include "cpw.mm"
include "wrex.mm"
include "dya2iocuni.mm"
include "wa.mm"
include "simpr.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "dya2iocct.mm"
include "ctex.mm"
include "mp1i.mm"
include "elpwi.mm"
include "ssct.mm"
include "sylancl.mm"
include "elsigagen2.mm"
include "syl3anc.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "rexlimiva.mm"
include "syl.mm"
include "ssriv.mm"
include "ax-mp.mm"
include "sigagenss2.mm"
include "mp3an.mm"

theorem sxbrsigalem1
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let vy: setvar y
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint n u
  disjoint n v
  disjoint R n
  disjoint R x
  disjoint J x
  disjoint n y
  disjoint u y
  disjoint v y
  disjoint x y
  disjoint R y
  assert |- ( sigaGen ` ( J tX J ) ) C_ ( sigaGen ` ran R )

  proof
    cJ
    cJ
    ctx
    co
    #
    cuni
    #
    cR
    crn
    #
    cuni
    #
    wceq
    @0
    @2
    csigagen
    cfv
    #
    wss
    @2
    cvv
    wcel
    #
    @0
    csigagen
    cfv
    @4
    wss
    @3
    cr
    cr
    cxp
    @1
    vx
    vv
    vu
    cR
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocucvr
    cJ
    cJ
    cr
    cr
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    sxbrsiga.0
    retop
    eqeltri
    #
    @7
    cr
    @6
    cuni
    cJ
    cuni
    uniretop
    cJ
    @6
    sxbrsiga.0
    unieqi
    eqtr4i
    #
    @8
    txunii
    eqtr2i
    vx
    @0
    @4
    vx
    cv
    #
    @0
    wcel
    vy
    cv
    #
    cuni
    #
    @9
    wceq
    #
    vy
    @2
    cpw
    #
    wrex
    @9
    @4
    wcel
    #
    vx
    vv
    vu
    @9
    cR
    vn
    cI
    cJ
    vy
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocuni
    @12
    @14
    vy
    @13
    @10
    @13
    wcel
    #
    @12
    wa
    @11
    @9
    @4
    @15
    @12
    simpr
    @15
    @11
    @4
    wcel
    #
    @12
    @15
    @5
    @10
    @2
    wss
    #
    @10
    com
    cdom
    wbr
    #
    @16
    @2
    com
    cdom
    wbr
    #
    @5
    @15
    vx
    vv
    vu
    cR
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocct
    #
    @2
    ctex
    #
    mp1i
    @10
    @2
    elpwi
    #
    @15
    @17
    @19
    @18
    @22
    @20
    @10
    @2
    ssct
    sylancl
    @2
    @10
    cvv
    elsigagen2
    syl3anc
    adantr
    eqeltrrd
    rexlimiva
    syl
    ssriv
    @19
    @5
    @20
    @21
    ax-mp
    @0
    @2
    cvv
    sigagenss2
    mp3an
end
