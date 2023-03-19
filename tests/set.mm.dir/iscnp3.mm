include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ccnv.mm"
include "iscnp.mm"
include "wb.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "ad2antlr.mm"
include "toponss.mm"
include "adantlr.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "syl2anc.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "3ad2ant1.mm"
include "bitrd.mm"

theorem iscnp3
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint P x
  disjoint P y
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ P e. X ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. K ( ( F ` P ) e. y -> E. x e. J ( P e. x /\ x C_ ( `' F " y ) ) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    cX
    cY
    cF
    wf
    #
    cP
    cF
    cfv
    vy
    cv
    #
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    cF
    @6
    cima
    @4
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    wa
    #
    @3
    @5
    @7
    @6
    cF
    ccnv
    @4
    cima
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    wa
    #
    vx
    vy
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp
    @0
    @1
    @13
    @19
    wb
    @2
    @0
    @3
    @12
    @18
    @0
    @3
    wa
    #
    @11
    @17
    vy
    cK
    @20
    @10
    @16
    @5
    @20
    @9
    @15
    vx
    cJ
    @20
    @6
    cJ
    wcel
    #
    wa
    #
    @8
    @14
    @7
    @22
    cF
    wfun
    #
    @6
    cF
    cdm
    #
    wss
    @8
    @14
    wb
    @3
    @23
    @0
    @21
    cX
    cY
    cF
    ffun
    ad2antlr
    @22
    @6
    cX
    @24
    @0
    @21
    @6
    cX
    wss
    @3
    @6
    cJ
    cX
    toponss
    adantlr
    @3
    @24
    cX
    wceq
    @0
    @21
    cX
    cY
    cF
    fdm
    ad2antlr
    sseqtr4d
    @6
    @4
    cF
    funimass3
    syl2anc
    anbi2d
    rexbidva
    imbi2d
    ralbidv
    pm5.32da
    3ad2ant1
    bitrd
end
