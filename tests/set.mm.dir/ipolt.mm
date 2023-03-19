include "wcel.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "wa.mm"
include "wss.mm"
include "wpss.mm"
include "eqid.mm"
include "ipole.mm"
include "anbi1d.mm"
include "wb.mm"
include "cvv.mm"
include "cipo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pltval.mm"
include "mp3an1.mm"
include "3adant1.mm"
include "df-pss.mm"
include "a1i.mm"
include "3bitr4d.mm"

theorem ipolt
  let c.lt: class .<
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ipolt.i: |- I = ( toInc ` F )
  assume ipolt.l: |- .< = ( lt ` I )


  assert |- ( ( F e. V /\ X e. F /\ Y e. F ) -> ( X .< Y <-> X C. Y ) )

  proof
    cF
    cV
    wcel
    #
    cX
    cF
    wcel
    #
    cY
    cF
    wcel
    #
    w3a
    #
    cX
    cY
    cI
    cple
    cfv
    #
    wbr
    #
    cX
    cY
    wne
    #
    wa
    #
    cX
    cY
    wss
    #
    @6
    wa
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    wpss
    #
    @3
    @5
    @8
    @6
    cF
    cI
    @4
    cV
    cX
    cY
    ipolt.i
    @4
    eqid
    #
    ipole
    anbi1d
    @1
    @2
    @10
    @7
    wb
    #
    @0
    cI
    cvv
    wcel
    @1
    @2
    @13
    cI
    cF
    cipo
    cfv
    cvv
    ipolt.i
    cF
    cipo
    fvex
    eqeltri
    cvv
    cF
    cF
    c.lt
    cI
    @4
    cX
    cY
    @12
    ipolt.l
    pltval
    mp3an1
    3adant1
    @11
    @9
    wb
    @3
    cX
    cY
    df-pss
    a1i
    3bitr4d
end
