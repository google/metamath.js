include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "wi.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "df-wlkson.mm"
include "copab.mm"
include "3simpc.mm"
include "wlkson.mm"
include "syl.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "3anbi1d.mm"
include "bropfvvvv.mm"
include "mp2an.mm"
include "3anass.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "wb.mm"
include "anim1i.mm"
include "iswlkon.mm"
include "biimpd.mm"
include "imdistani.mm"
include "mpancom.mm"

theorem wlkonprop
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume wlkson.v: |- V = ( Vtx ` G )


  assert |- ( F ( A ( WalksOn ` G ) B ) P -> ( ( G e. _V /\ A e. V /\ B e. V ) /\ ( F e. _V /\ P e. _V ) /\ ( F ( Walks ` G ) P /\ ( P ` 0 ) = A /\ ( P ` ( # ` F ) ) = B ) ) )

  proof
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    #
    wbr
    #
    cG
    cvv
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    cc0
    cP
    cfv
    cA
    wceq
    cF
    chash
    cfv
    cP
    cfv
    cB
    wceq
    w3a
    #
    wa
    #
    @5
    @6
    @9
    w3a
    @7
    @1
    @10
    @1
    @2
    @3
    @4
    wa
    #
    @6
    w3a
    #
    @7
    cV
    cvv
    wcel
    #
    @13
    @1
    @12
    wi
    cV
    cG
    cvtx
    cfv
    #
    cvv
    wlkson.v
    cG
    cvtx
    fvex
    eqeltri
    #
    @15
    vf
    cv
    #
    vp
    cv
    #
    vg
    cv
    #
    cwlks
    cfv
    #
    wbr
    #
    cc0
    @17
    cfv
    #
    va
    cv
    wceq
    #
    @16
    chash
    cfv
    @17
    cfv
    #
    vb
    cv
    wceq
    #
    w3a
    @16
    @17
    @8
    wbr
    #
    @22
    @24
    w3a
    @25
    @21
    cA
    wceq
    @23
    cB
    wceq
    w3a
    #
    cG
    cA
    cB
    cF
    cV
    cV
    cvv
    vp
    cP
    cwlkson
    @18
    cvtx
    cfv
    #
    @27
    cvv
    cvv
    vg
    va
    vb
    vf
    vf
    vg
    vp
    va
    vb
    df-wlkson
    @5
    @11
    @0
    @26
    vf
    vp
    copab
    wceq
    @2
    @3
    @4
    3simpc
    #
    cA
    cB
    vf
    cG
    cV
    vp
    wlkson.v
    wlkson
    syl
    @18
    cG
    wceq
    #
    @27
    @14
    cV
    @18
    cG
    cvtx
    fveq2
    wlkson.v
    syl6eqr
    #
    @30
    @29
    @20
    @25
    @22
    @24
    @29
    @19
    @8
    @16
    @17
    @18
    cG
    cwlks
    fveq2
    breqd
    3anbi1d
    bropfvvvv
    mp2an
    @7
    @2
    @11
    wa
    #
    @6
    wa
    @12
    @5
    @31
    @6
    @2
    @3
    @4
    3anass
    anbi1i
    @2
    @11
    @6
    df-3an
    bitr4i
    sylibr
    @7
    @1
    @9
    @7
    @1
    @9
    @7
    @11
    @6
    wa
    @1
    @9
    wb
    @5
    @11
    @6
    @28
    anim1i
    cA
    cB
    cP
    cvv
    cF
    cG
    cV
    cvv
    wlkson.v
    iswlkon
    syl
    biimpd
    imdistani
    mpancom
    @5
    @6
    @9
    df-3an
    sylibr
end
