include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0g.mm"
include "eqid.mm"
include "simprr.mm"
include "wceq.mm"
include "ressbas2.mm"
include "ad2antrl.mm"
include "eleqtrd.mm"
include "cv.mm"
include "co.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "ressplusg.mm"
include "syl.mm"
include "oveqd.mm"
include "simpll.mm"
include "ressbasss.mm"
include "sseli.mm"
include "mndlid.mm"
include "syl2an.mm"
include "eqtr3d.mm"
include "mndrid.mm"
include "ismgmid2.mm"

theorem submnd0
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let c.0: class .0.
  let vx: setvar x
  assume submnd0.b: |- B = ( Base ` G )
  assume submnd0.z: |- .0. = ( 0g ` G )
  assume submnd0.h: |- H = ( G |`s S )


  assert |- ( ( ( G e. Mnd /\ H e. Mnd ) /\ ( S C_ B /\ .0. e. S ) ) -> .0. = ( 0g ` H ) )

  proof
    cG
    cmnd
    wcel
    #
    cH
    cmnd
    wcel
    #
    wa
    #
    cS
    cB
    wss
    #
    c.0
    cS
    wcel
    #
    wa
    #
    wa
    #
    vx
    cH
    cbs
    cfv
    #
    cH
    cplusg
    cfv
    #
    c.0
    cH
    cH
    c0g
    cfv
    #
    @7
    eqid
    @9
    eqid
    @8
    eqid
    @6
    c.0
    cS
    @7
    @2
    @3
    @4
    simprr
    @3
    cS
    @7
    wceq
    @2
    @4
    cS
    cB
    cH
    cG
    submnd0.h
    submnd0.b
    ressbas2
    ad2antrl
    #
    eleqtrd
    @6
    vx
    cv
    #
    @7
    wcel
    #
    wa
    #
    c.0
    @11
    cG
    cplusg
    cfv
    #
    co
    #
    c.0
    @11
    @8
    co
    @11
    @13
    @14
    @8
    c.0
    @11
    @13
    cS
    cvv
    wcel
    #
    @14
    @8
    wceq
    @6
    @16
    @12
    @6
    cS
    @7
    cvv
    @10
    cH
    cbs
    fvex
    syl6eqel
    adantr
    cS
    @14
    cG
    cH
    cvv
    submnd0.h
    @14
    eqid
    #
    ressplusg
    syl
    #
    oveqd
    @6
    @0
    @11
    cB
    wcel
    #
    @15
    @11
    wceq
    @12
    @0
    @1
    @5
    simpll
    #
    @7
    cB
    @11
    cS
    cB
    cH
    cG
    submnd0.h
    submnd0.b
    ressbasss
    sseli
    #
    cB
    @14
    cG
    @11
    c.0
    submnd0.b
    @17
    submnd0.z
    mndlid
    syl2an
    eqtr3d
    @13
    @11
    c.0
    @14
    co
    #
    @11
    c.0
    @8
    co
    @11
    @13
    @14
    @8
    @11
    c.0
    @18
    oveqd
    @6
    @0
    @19
    @22
    @11
    wceq
    @12
    @20
    @21
    cB
    @14
    cG
    @11
    c.0
    submnd0.b
    @17
    submnd0.z
    mndrid
    syl2an
    eqtr3d
    ismgmid2
end
