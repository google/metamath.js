include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "con0.mm"
include "eqid.mm"
include "1on.mm"
include "a1i.mm"
include "simpl.mm"
include "cmpl.mm"
include "ply1mulr.mm"
include "mplmulr.mm"
include "mplbasss.mm"
include "ply1bascl2.mm"
include "sseldi.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "ply1vsca.mm"
include "mplvsca2.mm"
include "simpr1.mm"
include "psrass23l.mm"

theorem ply1ass23l
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  assume ply1ass23l.p: |- P = ( Poly1 ` R )
  assume ply1ass23l.t: |- .X. = ( .r ` P )
  assume ply1ass23l.b: |- B = ( Base ` P )
  assume ply1ass23l.k: |- K = ( Base ` R )
  assume ply1ass23l.n: |- .x. = ( .s ` P )


  assert |- ( ( R e. Ring /\ ( A e. K /\ X e. B /\ Y e. B ) ) -> ( ( A .x. X ) .X. Y ) = ( A .x. ( X .X. Y ) ) )

  proof
    cR
    crg
    wcel
    #
    cA
    cK
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cA
    c1o
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    c1o
    cmap
    co
    crab
    #
    cR
    @6
    c.x
    c.xp
    vf
    c1o
    cK
    con0
    cX
    cY
    @6
    eqid
    #
    c1o
    con0
    wcel
    @5
    1on
    a1i
    @0
    @4
    simpl
    @8
    eqid
    cR
    @6
    c.xp
    c1o
    c1o
    cR
    cmpl
    co
    #
    @10
    eqid
    #
    @9
    cR
    @10
    c.xp
    cP
    ply1ass23l.p
    @11
    ply1ass23l.t
    ply1mulr
    mplmulr
    @7
    eqid
    #
    @4
    cX
    @7
    wcel
    #
    @0
    @2
    @1
    @13
    @3
    @2
    @10
    cbs
    cfv
    #
    @7
    cX
    @7
    @10
    cR
    @6
    @14
    c1o
    @11
    @9
    @14
    eqid
    @12
    mplbasss
    #
    cB
    cP
    cR
    cX
    ply1ass23l.p
    ply1ass23l.b
    ply1bascl2
    sseldi
    3ad2ant2
    adantl
    @4
    cY
    @7
    wcel
    #
    @0
    @3
    @1
    @16
    @2
    @3
    @14
    @7
    cY
    @15
    cB
    cP
    cR
    cY
    ply1ass23l.p
    ply1ass23l.b
    ply1bascl2
    sseldi
    3ad2ant3
    adantl
    ply1ass23l.k
    @10
    cR
    @6
    c.x
    c1o
    @11
    @9
    cR
    @10
    c.x
    cP
    ply1ass23l.p
    @11
    ply1ass23l.n
    ply1vsca
    mplvsca2
    @0
    @1
    @2
    @3
    simpr1
    psrass23l
end
