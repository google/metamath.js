include "ccring.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "wa.mm"
include "cdif.mm"
include "co.mm"
include "w3a.mm"
include "wn.mm"
include "eldifn.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "wi.mm"
include "eldifi.mm"
include "pridlc.mm"
include "ord.mm"
include "syl3anr1.mm"
include "mpd.mm"

theorem pridlc2
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


  assert |- ( ( ( R e. CRingOps /\ P e. ( PrIdl ` R ) ) /\ ( A e. ( X \ P ) /\ B e. X /\ ( A H B ) e. P ) ) -> B e. P )

  proof
    cR
    ccring
    wcel
    cP
    cR
    cpridl
    cfv
    wcel
    wa
    #
    cA
    cX
    cP
    cdif
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cH
    co
    cP
    wcel
    #
    w3a
    #
    wa
    cA
    cP
    wcel
    #
    wn
    #
    cB
    cP
    wcel
    #
    @4
    @6
    @0
    @1
    @2
    @6
    @3
    cA
    cX
    cP
    eldifn
    3ad2ant1
    adantl
    @1
    cA
    cX
    wcel
    #
    @0
    @2
    @3
    @6
    @7
    wi
    cA
    cX
    cP
    eldifi
    @0
    @8
    @2
    @3
    w3a
    wa
    @5
    @7
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
    pridlc
    ord
    syl3anr1
    mpd
end
