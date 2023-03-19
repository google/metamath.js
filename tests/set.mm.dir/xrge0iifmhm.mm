include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cxrs.mm"
include "cpnf.mm"
include "cmhm.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cmul.mm"
include "cxad.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "ctmd.mm"
include "eqid.mm"
include "iistmd.mm"
include "tmdmnd.mm"
include "ax-mp.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "cmnmnd.mm"
include "pm3.2i.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cneg.mm"
include "ce.mm"
include "cif.mm"
include "cmpt.mm"
include "xrge0iifcnv.mm"
include "simpli.mm"
include "f1of.mm"
include "xrge0iifhom.mm"
include "rgen2a.mm"
include "xrge0iif1.mm"
include "3pm3.2i.mm"
include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "unitsscn.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "xrge0base.mm"
include "cvv.mm"
include "cnfldex.mm"
include "ovex.mm"
include "mgpress.mm"
include "mp2an.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "mgpplusg.mm"
include "xrge0plusg.mm"
include "crg.mm"
include "c0g.mm"
include "cnring.mm"
include "1elunit.mm"
include "cnfld1.mm"
include "ringidss.mm"
include "mp3an.mm"
include "xrge00.mm"
include "ismhm.mm"
include "mpbir2an.mm"

theorem xrge0iifmhm
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let vy: setvar y
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let vu: setvar u
  let cY: class Y
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )
  assume xrge0iifhmeo.k: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )

  disjoint F x
  disjoint x y
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint u x
  disjoint Y x
  assert |- F e. ( ( ( mulGrp ` CCfld ) |`s ( 0 [,] 1 ) ) MndHom ( RR*s |`s ( 0 [,] +oo ) ) )

  proof
    cF
    ccnfld
    cmgp
    cfv
    #
    cc0
    c1
    cicc
    co
    #
    cress
    co
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    cmhm
    co
    wcel
    @2
    cmnd
    wcel
    #
    @4
    cmnd
    wcel
    #
    wa
    @1
    @3
    cF
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    cmul
    co
    cF
    cfv
    @8
    cF
    cfv
    @9
    cF
    cfv
    cxad
    co
    wceq
    #
    vz
    @1
    wral
    vy
    @1
    wral
    #
    c1
    cF
    cfv
    cc0
    wceq
    #
    w3a
    @5
    @6
    @2
    ctmd
    wcel
    @5
    @2
    @2
    eqid
    #
    iistmd
    @2
    tmdmnd
    ax-mp
    @4
    ccmn
    wcel
    @6
    xrge0cmn
    @4
    cmnmnd
    ax-mp
    pm3.2i
    @7
    @11
    @12
    @1
    @3
    cF
    wf1o
    #
    @7
    @14
    cF
    ccnv
    vy
    @3
    @8
    cpnf
    wceq
    cc0
    @8
    cneg
    ce
    cfv
    cif
    cmpt
    wceq
    vx
    vy
    cF
    xrge0iifhmeo.1
    xrge0iifcnv
    simpli
    @1
    @3
    cF
    f1of
    ax-mp
    @10
    vy
    vz
    @1
    vx
    cF
    cJ
    @8
    @9
    xrge0iifhmeo.1
    xrge0iifhmeo.k
    xrge0iifhom
    rgen2a
    vx
    cF
    cJ
    xrge0iifhmeo.1
    xrge0iifhmeo.k
    xrge0iif1
    3pm3.2i
    vy
    vz
    @1
    @3
    cmul
    cxad
    @2
    @4
    cF
    cc0
    c1
    @1
    cc
    wss
    #
    @1
    @2
    cbs
    cfv
    wceq
    unitsscn
    @1
    cc
    @2
    @0
    @13
    cc
    ccnfld
    @0
    @0
    eqid
    #
    cnfldbas
    mgpbas
    ressbas2
    ax-mp
    xrge0base
    ccnfld
    @1
    cress
    co
    #
    cmul
    @2
    ccnfld
    cvv
    wcel
    @1
    cvv
    wcel
    #
    @2
    @17
    cmgp
    cfv
    wceq
    cnfldex
    cc0
    c1
    cicc
    ovex
    #
    @1
    ccnfld
    @17
    @0
    cvv
    cvv
    @17
    eqid
    #
    @16
    mgpress
    mp2an
    @18
    cmul
    @17
    cmulr
    cfv
    wceq
    @19
    @1
    ccnfld
    @17
    cmul
    cvv
    @20
    cnfldmul
    ressmulr
    ax-mp
    mgpplusg
    xrge0plusg
    ccnfld
    crg
    wcel
    @15
    c1
    @1
    wcel
    c1
    @2
    c0g
    cfv
    wceq
    cnring
    unitsscn
    1elunit
    @1
    cc
    ccnfld
    c1
    @2
    @13
    cnfldbas
    cnfld1
    ringidss
    mp3an
    xrge00
    ismhm
    mpbir2an
end
