include "ccring.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "wa.mm"
include "cdif.mm"
include "co.mm"
include "crngo.mm"
include "crngorngo.mm"
include "eldifi.mm"
include "anim12i.mm"
include "rngocl.mm"
include "3expb.mm"
include "syl2an.mm"
include "adantlr.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antll.mm"
include "wi.mm"
include "pridlc2.mm"
include "3exp2.mm"
include "imp32.mm"
include "con3d.mm"
include "sylanr2.mm"
include "mpd.mm"
include "eldifd.mm"

theorem pridlc3
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vs: setvar s
  assume ispridlc.1: |- G = ( 1st ` R )
  assume ispridlc.2: |- H = ( 2nd ` R )
  assume ispridlc.3: |- X = ran G


  assert |- ( ( ( R e. CRingOps /\ P e. ( PrIdl ` R ) ) /\ ( A e. ( X \ P ) /\ B e. ( X \ P ) ) ) -> ( A H B ) e. ( X \ P ) )

  proof
    cR
    ccring
    wcel
    #
    cP
    cR
    cpridl
    cfv
    wcel
    #
    wa
    #
    cA
    cX
    cP
    cdif
    #
    wcel
    #
    cB
    @3
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cH
    co
    #
    cX
    cP
    @0
    @6
    @8
    cX
    wcel
    #
    @1
    @0
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    @9
    @6
    cR
    crngorngo
    @4
    @11
    @5
    @12
    cA
    cX
    cP
    eldifi
    cB
    cX
    cP
    eldifi
    #
    anim12i
    @10
    @11
    @12
    @9
    cA
    cB
    cR
    cG
    cH
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    rngocl
    3expb
    syl2an
    adantlr
    @7
    cB
    cP
    wcel
    #
    wn
    #
    @8
    cP
    wcel
    #
    wn
    #
    @5
    @15
    @2
    @4
    cB
    cX
    cP
    eldifn
    ad2antll
    @5
    @2
    @4
    @12
    @15
    @17
    wi
    @13
    @2
    @4
    @12
    wa
    wa
    @16
    @14
    @2
    @4
    @12
    @16
    @14
    wi
    @2
    @4
    @12
    @16
    @14
    cA
    cB
    cP
    cR
    cG
    cH
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    pridlc2
    3exp2
    imp32
    con3d
    sylanr2
    mpd
    eldifd
end
