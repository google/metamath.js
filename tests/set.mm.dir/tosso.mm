include "wcel.mm"
include "cpo.mm"
include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wral.mm"
include "wa.mm"
include "wpo.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "weq.mm"
include "w3o.mm"
include "ctos.mm"
include "wor.mm"
include "wb.mm"
include "pleval2.mm"
include "3expb.mm"
include "w3a.mm"
include "equcom.mm"
include "orbi2i.mm"
include "syl6bb.mm"
include "3com23.mm"
include "orbi12d.mm"
include "df-3or.mm"
include "or32.mm"
include "orordir.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "2ralbidva.mm"
include "pm5.32i.mm"
include "pospo.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "istos.mm"
include "df-so.mm"
include "anbi1i.mm"
include "an32.mm"
include "3bitr4g.mm"

theorem tosso
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tosso.b: |- B = ( Base ` K )
  assume tosso.l: |- .<_ = ( le ` K )
  assume tosso.s: |- .< = ( lt ` K )


  assert |- ( K e. V -> ( K e. Toset <-> ( .< Or B /\ ( _I |` B ) C_ .<_ ) ) )

  proof
    cK
    cV
    wcel
    #
    cK
    cpo
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    @3
    @2
    c.le
    wbr
    #
    wo
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    cB
    c.lt
    wpo
    #
    cid
    cB
    cres
    c.le
    wss
    #
    wa
    #
    @2
    @3
    c.lt
    wbr
    #
    vx
    vy
    weq
    #
    @3
    @2
    c.lt
    wbr
    #
    w3o
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    cK
    ctos
    wcel
    cB
    c.lt
    wor
    #
    @10
    wa
    #
    @8
    @1
    @16
    wa
    @0
    @17
    @1
    @7
    @16
    @1
    @6
    @15
    vx
    vy
    cB
    cB
    @1
    @2
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    wa
    #
    @6
    @12
    @13
    wo
    #
    @14
    @13
    wo
    #
    wo
    #
    @15
    @22
    @4
    @23
    @5
    @24
    @1
    @20
    @21
    @4
    @23
    wb
    cB
    c.lt
    cK
    c.le
    @2
    @3
    tosso.b
    tosso.l
    tosso.s
    pleval2
    3expb
    @1
    @20
    @21
    @5
    @24
    wb
    #
    @1
    @21
    @20
    @26
    @1
    @21
    @20
    w3a
    @5
    @14
    vy
    vx
    weq
    #
    wo
    @24
    cB
    c.lt
    cK
    c.le
    @3
    @2
    tosso.b
    tosso.l
    tosso.s
    pleval2
    @27
    @13
    @14
    vy
    vx
    equcom
    orbi2i
    syl6bb
    3com23
    3expb
    orbi12d
    @15
    @23
    @14
    wo
    #
    @25
    @12
    @13
    @14
    df-3or
    @28
    @12
    @14
    wo
    @13
    wo
    @25
    @12
    @13
    @14
    or32
    @12
    @14
    @13
    orordir
    bitri
    bitri
    syl6bbr
    2ralbidva
    pm5.32i
    @0
    @1
    @11
    @16
    cB
    c.lt
    cK
    c.le
    cV
    tosso.b
    tosso.l
    tosso.s
    pospo
    anbi1d
    syl5bb
    vx
    vy
    cB
    cK
    c.le
    tosso.b
    tosso.l
    istos
    @19
    @9
    @16
    wa
    #
    @10
    wa
    @17
    @18
    @29
    @10
    vx
    vy
    cB
    c.lt
    df-so
    anbi1i
    @9
    @16
    @10
    an32
    bitri
    3bitr4g
end
