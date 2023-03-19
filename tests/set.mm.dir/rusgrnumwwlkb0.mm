include "cuspgr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "crab.mm"
include "chash.mm"
include "cs1.mm"
include "csn.mm"
include "c1.mm"
include "cn0.mm"
include "simpr.mm"
include "0nn0.mm"
include "rusgrnumwwlklem.mm"
include "sylancl.mm"
include "cab.mm"
include "cvtx.mm"
include "cword.mm"
include "df-rab.mm"
include "a1i.mm"
include "wwlksn0s.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "abbidv.mm"
include "wb.mm"
include "w3a.mm"
include "wrdl1s1.mm"
include "df-3an.mm"
include "syl6rbb.mm"
include "vex.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "elab.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eleq2s.mm"
include "eqrdv.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "s1cl.mm"
include "hashsng.mm"
include "syl.mm"

theorem rusgrnumwwlkb0
  let vw: setvar w
  let vv: setvar v
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cL: class L
  let cV: class V
  let cN: class N
  assume rusgrnumwwlk.v: |- V = ( Vtx ` G )
  assume rusgrnumwwlk.l: |- L = ( v e. V , n e. NN0 |-> ( # ` { w e. ( n WWalksN G ) | ( w ` 0 ) = v } ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint P n
  disjoint P v
  disjoint P w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint N n
  disjoint N v
  disjoint N w
  assert |- ( ( G e. USPGraph /\ P e. V ) -> ( P L 0 ) = 1 )

  proof
    cG
    cuspgr
    wcel
    #
    cP
    cV
    wcel
    #
    wa
    #
    cP
    cc0
    cL
    co
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    #
    vw
    cc0
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    #
    cP
    cs1
    #
    csn
    #
    chash
    cfv
    #
    c1
    @2
    @1
    cc0
    cn0
    wcel
    @3
    @9
    wceq
    @0
    @1
    simpr
    0nn0
    vw
    vv
    cP
    vn
    cG
    cL
    cc0
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlklem
    sylancl
    @2
    @8
    @11
    chash
    @2
    @8
    @4
    @7
    wcel
    #
    @6
    wa
    #
    vw
    cab
    #
    @4
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @4
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @6
    wa
    #
    vw
    cab
    #
    @11
    @8
    @15
    wceq
    @2
    @6
    vw
    @7
    df-rab
    a1i
    @2
    @14
    @22
    vw
    @2
    @13
    @21
    @6
    @2
    @13
    @4
    @20
    vw
    @17
    crab
    #
    wcel
    @21
    @2
    @7
    @24
    @4
    @7
    @24
    wceq
    @2
    vw
    cG
    wwlksn0s
    a1i
    eleq2d
    @20
    vw
    @17
    rabid
    syl6bb
    anbi1d
    abbidv
    @1
    @23
    @11
    wceq
    @0
    @1
    vv
    @23
    @11
    vv
    cv
    #
    @23
    wcel
    #
    @25
    @11
    wcel
    #
    wb
    cP
    @16
    cV
    cP
    @16
    wcel
    #
    @25
    @17
    wcel
    #
    @25
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cc0
    @25
    cfv
    #
    cP
    wceq
    #
    wa
    #
    @25
    @10
    wceq
    #
    @26
    @27
    @28
    @36
    @29
    @31
    @34
    w3a
    @35
    cP
    @16
    @25
    wrdl1s1
    @29
    @31
    @34
    df-3an
    syl6rbb
    @22
    @35
    vw
    @25
    vv
    vex
    @4
    @25
    wceq
    #
    @21
    @32
    @6
    @34
    @37
    @18
    @29
    @20
    @31
    @4
    @25
    @17
    eleq1
    @37
    @19
    @30
    c1
    @4
    @25
    chash
    fveq2
    eqeq1d
    anbi12d
    @37
    @5
    @33
    cP
    cc0
    @4
    @25
    fveq1
    eqeq1d
    anbi12d
    elab
    vv
    @10
    velsn
    3bitr4g
    rusgrnumwwlk.v
    eleq2s
    eqrdv
    adantl
    3eqtrd
    fveq2d
    @1
    @12
    c1
    wceq
    #
    @0
    @1
    @10
    cV
    cword
    #
    wcel
    @38
    cP
    cV
    s1cl
    @10
    @39
    hashsng
    syl
    adantl
    3eqtrd
end
