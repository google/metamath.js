include "cn0.mm"
include "wcel.mm"
include "cwwlksn.mm"
include "co.mm"
include "cwwlks.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "cv.mm"
include "cpr.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "iswwlksn.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "iswwlks.mm"
include "df-3an.mm"
include "nn0p1gt0.mm"
include "gt0ne0d.mm"
include "adantr.mm"
include "neeq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "syl5ibcom.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem iswwlksnx
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume iswwlksnx.v: |- V = ( Vtx ` G )
  assume iswwlksnx.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  assert |- ( N e. NN0 -> ( W e. ( N WWalksN G ) <-> ( W e. Word V /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ ( # ` W ) = ( N + 1 ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    cW
    cG
    cwwlks
    cfv
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    cW
    cV
    cword
    #
    wcel
    #
    vi
    cv
    #
    cW
    cfv
    @8
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @2
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    @4
    w3a
    #
    cG
    cN
    cW
    iswwlksn
    @0
    @5
    @7
    @9
    wa
    #
    @4
    wa
    @10
    @0
    @4
    @1
    @11
    @0
    @4
    @1
    @11
    wb
    @1
    cW
    c0
    wne
    #
    @7
    @9
    w3a
    #
    @0
    @4
    wa
    #
    @11
    vi
    cE
    cG
    cV
    cW
    iswwlksnx.v
    iswwlksnx.e
    iswwlks
    @13
    @12
    @7
    wa
    #
    @9
    wa
    @14
    @11
    @12
    @7
    @9
    df-3an
    @14
    @15
    @7
    @9
    @14
    @7
    @15
    @14
    @7
    @12
    @14
    @2
    cc0
    wne
    #
    @7
    @12
    @14
    @16
    @3
    cc0
    wne
    #
    @0
    @17
    @4
    @0
    @3
    cN
    nn0p1gt0
    gt0ne0d
    adantr
    @4
    @16
    @17
    wb
    @0
    @2
    @3
    cc0
    neeq1
    adantl
    mpbird
    @7
    @2
    cc0
    cW
    c0
    cW
    @6
    hasheq0
    necon3bid
    syl5ibcom
    pm4.71rd
    bicomd
    anbi1d
    syl5bb
    syl5bb
    ex
    pm5.32rd
    @7
    @9
    @4
    df-3an
    syl6bbr
    bitrd
end
