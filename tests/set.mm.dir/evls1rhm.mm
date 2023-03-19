include "ccrg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "ces.mm"
include "crh.mm"
include "cpw.mm"
include "wceq.mm"
include "wss.mm"
include "subrgss.mm"
include "adantl.mm"
include "wb.mm"
include "elpwg.mm"
include "mpbird.mm"
include "eqid.mm"
include "evls1fval.mm"
include "syldan.mm"
include "cpws.mm"
include "evls1rhmlem.mm"
include "adantr.mm"
include "cmpl.mm"
include "con0.mm"
include "1on.mm"
include "evlsrhm.mm"
include "mp3an1.mm"
include "cbs.mm"
include "eqidd.mm"
include "cps1.mm"
include "ply1bas.mm"
include "a1i.mm"
include "cplusg.mm"
include "ply1plusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "ply1mulr.mm"
include "rhmpropd.mm"
include "eleqtrrd.mm"
include "rhmco.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem evls1rhm
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume evls1rhm.q: |- Q = ( S evalSub1 R )
  assume evls1rhm.b: |- B = ( Base ` S )
  assume evls1rhm.t: |- T = ( S ^s B )
  assume evls1rhm.u: |- U = ( S |`s R )
  assume evls1rhm.w: |- W = ( Poly1 ` U )


  assert |- ( ( S e. CRing /\ R e. ( SubRing ` S ) ) -> Q e. ( W RingHom T ) )

  proof
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    #
    wcel
    #
    wa
    #
    cQ
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
    cR
    c1o
    cS
    ces
    co
    #
    cfv
    #
    ccom
    #
    cW
    cT
    crh
    co
    #
    @0
    @2
    cR
    cB
    cpw
    wcel
    #
    cQ
    @10
    wceq
    @3
    @12
    cR
    cB
    wss
    #
    @2
    @13
    @0
    cR
    cB
    cS
    evls1rhm.b
    subrgss
    adantl
    @2
    @12
    @13
    wb
    @0
    cR
    cB
    @1
    elpwg
    adantl
    mpbird
    vx
    vy
    cB
    cQ
    cR
    cS
    @8
    ccrg
    evls1rhm.q
    @8
    eqid
    evls1rhm.b
    evls1fval
    syldan
    @3
    @7
    cS
    @4
    cpws
    co
    #
    cT
    crh
    co
    wcel
    #
    @9
    cW
    @14
    crh
    co
    #
    wcel
    @10
    @11
    wcel
    @0
    @15
    @2
    vx
    vy
    cB
    cS
    cT
    @7
    evls1rhm.b
    evls1rhm.t
    @7
    eqid
    evls1rhmlem
    adantr
    @3
    @9
    c1o
    cU
    cmpl
    co
    #
    @14
    crh
    co
    #
    @16
    c1o
    con0
    wcel
    @0
    @2
    @9
    @18
    wcel
    1on
    cB
    @9
    cR
    cS
    @14
    cU
    c1o
    con0
    @17
    @9
    eqid
    @17
    eqid
    #
    evls1rhm.u
    @14
    eqid
    evls1rhm.b
    evlsrhm
    mp3an1
    @3
    vx
    vy
    cW
    cbs
    cfv
    #
    @14
    cbs
    cfv
    #
    cW
    @14
    @17
    @14
    @3
    @20
    eqidd
    @3
    @21
    eqidd
    #
    @20
    @17
    cbs
    cfv
    wceq
    @3
    cW
    cU
    cU
    cps1
    cfv
    #
    @20
    evls1rhm.w
    @23
    eqid
    @20
    eqid
    ply1bas
    a1i
    @22
    @3
    @5
    @20
    wcel
    @6
    @20
    wcel
    wa
    #
    vx
    vy
    cW
    cplusg
    cfv
    #
    @17
    cplusg
    cfv
    #
    @25
    @26
    wceq
    @3
    @25
    cU
    @17
    cW
    evls1rhm.w
    @19
    @25
    eqid
    ply1plusg
    a1i
    oveqdr
    @3
    @5
    @21
    wcel
    @6
    @21
    wcel
    wa
    wa
    #
    @5
    @6
    @14
    cplusg
    cfv
    co
    eqidd
    @3
    @24
    vx
    vy
    cW
    cmulr
    cfv
    #
    @17
    cmulr
    cfv
    #
    @28
    @29
    wceq
    @3
    cU
    @17
    @28
    cW
    evls1rhm.w
    @19
    @28
    eqid
    ply1mulr
    a1i
    oveqdr
    @27
    @5
    @6
    @14
    cmulr
    cfv
    co
    eqidd
    rhmpropd
    eleqtrrd
    cW
    @14
    cT
    @7
    @9
    rhmco
    syl2anc
    eqeltrd
end
