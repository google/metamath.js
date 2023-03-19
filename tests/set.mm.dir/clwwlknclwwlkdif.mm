include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "clsw.mm"
include "wne.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cdif.mm"
include "wn.mm"
include "cwwlksnon.mm"
include "cvtx.mm"
include "eqid.mm"
include "iswwlksnon.mm"
include "eqtri.mm"
include "difeq12i.mm"
include "difrab.mm"
include "wcel.mm"
include "annotanannot.mm"
include "df-ne.mm"
include "wwlknlsw.mm"
include "neeq1d.mm"
include "syl5bbr.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "rabbiia.mm"
include "3eqtrri.mm"

theorem clwwlknclwwlkdif
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cN: class N
  let cX: class X
  assume clwwlknclwwlkdif.a: |- A = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = X /\ ( lastS ` w ) =/= X ) }
  assume clwwlknclwwlkdif.b: |- B = ( X ( N WWalksNOn G ) X )
  assume clwwlknclwwlkdif.c: |- C = { w e. ( N WWalksN G ) | ( w ` 0 ) = X }

  disjoint G w
  disjoint N w
  disjoint X w
  assert |- A = ( C \ B )

  proof
    cA
    cc0
    vw
    cv
    #
    cfv
    cX
    wceq
    #
    @0
    clsw
    cfv
    #
    cX
    wne
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    cC
    cB
    cdif
    #
    clwwlknclwwlkdif.a
    @7
    @1
    vw
    @5
    crab
    #
    @1
    cN
    @0
    cfv
    #
    cX
    wceq
    #
    wa
    #
    vw
    @5
    crab
    #
    cdif
    @1
    @11
    wn
    wa
    #
    vw
    @5
    crab
    @6
    cC
    @8
    cB
    @12
    clwwlknclwwlkdif.c
    cB
    cX
    cX
    cN
    cG
    cwwlksnon
    co
    co
    @12
    clwwlknclwwlkdif.b
    vw
    cX
    cX
    cG
    cN
    cG
    cvtx
    cfv
    #
    @14
    eqid
    iswwlksnon
    eqtri
    difeq12i
    @1
    @11
    vw
    @5
    difrab
    @13
    @4
    vw
    @5
    @13
    @1
    @10
    wn
    #
    wa
    @0
    @5
    wcel
    #
    @4
    @1
    @10
    annotanannot
    @16
    @15
    @3
    @1
    @15
    @9
    cX
    wne
    @16
    @3
    @9
    cX
    df-ne
    @16
    @9
    @2
    cX
    cG
    cN
    @0
    wwlknlsw
    neeq1d
    syl5bbr
    anbi2d
    syl5bb
    rabbiia
    3eqtrri
    eqtri
end
