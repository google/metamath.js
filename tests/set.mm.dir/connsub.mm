include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "wi.mm"
include "wral.mm"
include "cdif.mm"
include "wn.mm"
include "connsuba.mm"
include "wb.mm"
include "inss1.mm"
include "toponss.mm"
include "ad2ant2r.mm"
include "syl5ss.mm"
include "reldisj.mm"
include "syl.mm"
include "3anbi3d.mm"
include "sseqin2.mm"
include "a1i.mm"
include "bicomd.mm"
include "necon3abid.mm"
include "imbi12d.mm"
include "2ralbidva.mm"
include "bitrd.mm"

theorem connsub
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let cA: class A

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint J u
  disjoint J v
  disjoint X u
  disjoint X v
  assert |- ( ( J e. ( TopOn ` X ) /\ S C_ X ) -> ( ( J |`t S ) e. Conn <-> A. x e. J A. y e. J ( ( ( x i^i S ) =/= (/) /\ ( y i^i S ) =/= (/) /\ ( x i^i y ) C_ ( X \ S ) ) -> -. S C_ ( x u. y ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cJ
    cS
    crest
    co
    cconn
    wcel
    vx
    cv
    #
    cS
    cin
    c0
    wne
    #
    vy
    cv
    #
    cS
    cin
    c0
    wne
    #
    @3
    @5
    cin
    #
    cS
    cin
    c0
    wceq
    #
    w3a
    #
    @3
    @5
    cun
    #
    cS
    cin
    #
    cS
    wne
    #
    wi
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    @4
    @6
    @7
    cX
    cS
    cdif
    wss
    #
    w3a
    #
    cS
    @10
    wss
    #
    wn
    #
    wi
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    vx
    vy
    cS
    cJ
    cX
    connsuba
    @2
    @13
    @18
    vx
    vy
    cJ
    cJ
    @2
    @3
    cJ
    wcel
    #
    @5
    cJ
    wcel
    #
    wa
    wa
    #
    @9
    @15
    @12
    @17
    @21
    @8
    @14
    @4
    @6
    @21
    @7
    cX
    wss
    @8
    @14
    wb
    @21
    @7
    @3
    cX
    @3
    @5
    inss1
    @0
    @19
    @3
    cX
    wss
    @1
    @20
    @3
    cJ
    cX
    toponss
    ad2ant2r
    syl5ss
    @7
    cS
    cX
    reldisj
    syl
    3anbi3d
    @21
    @16
    @11
    cS
    @21
    @16
    @11
    cS
    wceq
    #
    @16
    @22
    wb
    @21
    cS
    @10
    sseqin2
    a1i
    bicomd
    necon3abid
    imbi12d
    2ralbidva
    bitrd
end
