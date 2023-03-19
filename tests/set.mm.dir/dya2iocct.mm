include "crn.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cz.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "cmpt2.mm"
include "cn.mm"
include "cen.mm"
include "znnen.mm"
include "nnct.mm"
include "endomtr.mm"
include "mp2an.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "rgen2w.mm"
include "mpt2cti.mm"
include "eqbrtri.mm"
include "rnct.mm"
include "ax-mp.mm"
include "wa.mm"
include "cxp.mm"
include "vex.mm"
include "xpex.mm"
include "breq1i.mm"
include "biimpri.mm"
include "3syl.mm"

theorem dya2iocct
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  assert |- ran R ~<_ _om

  proof
    cI
    crn
    #
    com
    cdom
    wbr
    #
    @1
    cR
    crn
    com
    cdom
    wbr
    #
    cI
    com
    cdom
    wbr
    @1
    cI
    vx
    vn
    cz
    cz
    vx
    cv
    #
    c2
    vn
    cv
    cexp
    co
    #
    cdiv
    co
    #
    @3
    c1
    caddc
    co
    @4
    cdiv
    co
    #
    cico
    co
    #
    cmpt2
    #
    com
    cdom
    dya2ioc.1
    cz
    com
    cdom
    wbr
    #
    @9
    @8
    com
    cdom
    wbr
    cz
    cn
    cen
    wbr
    cn
    com
    cdom
    wbr
    @9
    znnen
    nnct
    cz
    cn
    com
    endomtr
    mp2an
    #
    @10
    vx
    vn
    cz
    cz
    @7
    cvv
    @7
    cvv
    wcel
    vx
    vn
    cz
    cz
    @5
    @6
    cico
    ovex
    rgen2w
    mpt2cti
    mp2an
    eqbrtri
    cI
    rnct
    ax-mp
    #
    @11
    @1
    @1
    wa
    vu
    vv
    @0
    @0
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    cmpt2
    #
    com
    cdom
    wbr
    #
    cR
    com
    cdom
    wbr
    #
    @2
    vu
    vv
    @0
    @0
    @14
    cvv
    @14
    cvv
    wcel
    vu
    vv
    @0
    @0
    @12
    @13
    vu
    vex
    vv
    vex
    xpex
    rgen2w
    mpt2cti
    @17
    @16
    cR
    @15
    com
    cdom
    dya2ioc.2
    breq1i
    biimpri
    cR
    rnct
    3syl
    mp2an
end
