include "ccrg.mm"
include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cevl.mm"
include "crh.mm"
include "eqid.mm"
include "evl1fval.mm"
include "cpws.mm"
include "evls1rhmlem.mm"
include "cmpl.mm"
include "con0.mm"
include "1on.mm"
include "evlrhm.mm"
include "mpan.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "wceq.mm"
include "cps1.mm"
include "ply1bas.mm"
include "a1i.mm"
include "wa.mm"
include "cplusg.mm"
include "ply1plusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "ply1mulr.mm"
include "rhmpropd.mm"
include "eleqtrrd.mm"
include "rhmco.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem evl1rhm
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume evl1rhm.q: |- O = ( eval1 ` R )
  assume evl1rhm.w: |- P = ( Poly1 ` R )
  assume evl1rhm.t: |- T = ( R ^s B )
  assume evl1rhm.b: |- B = ( Base ` R )


  assert |- ( R e. CRing -> O e. ( P RingHom T ) )

  proof
    cR
    ccrg
    wcel
    #
    cO
    vx
    cB
    cB
    c1o
    cmap
    co
    #
    cmap
    co
    vx
    cv
    #
    vy
    cB
    c1o
    vy
    cv
    #
    csn
    cxp
    cmpt
    ccom
    cmpt
    #
    c1o
    cR
    cevl
    co
    #
    ccom
    #
    cP
    cT
    crh
    co
    #
    vx
    vy
    cB
    @5
    cR
    cO
    evl1rhm.q
    @5
    eqid
    #
    evl1rhm.b
    evl1fval
    @0
    @4
    cR
    @1
    cpws
    co
    #
    cT
    crh
    co
    wcel
    @5
    cP
    @9
    crh
    co
    #
    wcel
    @6
    @7
    wcel
    vx
    vy
    cB
    cR
    cT
    @4
    evl1rhm.b
    evl1rhm.t
    @4
    eqid
    evls1rhmlem
    @0
    @5
    c1o
    cR
    cmpl
    co
    #
    @9
    crh
    co
    #
    @10
    c1o
    con0
    wcel
    @0
    @5
    @12
    wcel
    1on
    cB
    @5
    cR
    @9
    c1o
    con0
    @11
    @8
    evl1rhm.b
    @11
    eqid
    #
    @9
    eqid
    evlrhm
    mpan
    @0
    vx
    vy
    cP
    cbs
    cfv
    #
    @9
    cbs
    cfv
    #
    cP
    @9
    @11
    @9
    @0
    @14
    eqidd
    @0
    @15
    eqidd
    #
    @14
    @11
    cbs
    cfv
    wceq
    @0
    cP
    cR
    cR
    cps1
    cfv
    #
    @14
    evl1rhm.w
    @17
    eqid
    @14
    eqid
    ply1bas
    a1i
    @16
    @0
    @2
    @14
    wcel
    @3
    @14
    wcel
    wa
    #
    vx
    vy
    cP
    cplusg
    cfv
    #
    @11
    cplusg
    cfv
    #
    @19
    @20
    wceq
    @0
    @19
    cR
    @11
    cP
    evl1rhm.w
    @13
    @19
    eqid
    ply1plusg
    a1i
    oveqdr
    @0
    @2
    @15
    wcel
    @3
    @15
    wcel
    wa
    wa
    #
    @2
    @3
    @9
    cplusg
    cfv
    co
    eqidd
    @0
    @18
    vx
    vy
    cP
    cmulr
    cfv
    #
    @11
    cmulr
    cfv
    #
    @22
    @23
    wceq
    @0
    cR
    @11
    @22
    cP
    evl1rhm.w
    @13
    @22
    eqid
    ply1mulr
    a1i
    oveqdr
    @21
    @2
    @3
    @9
    cmulr
    cfv
    co
    eqidd
    rhmpropd
    eleqtrrd
    cP
    @9
    cT
    @4
    @5
    rhmco
    syl2anc
    syl5eqel
end
