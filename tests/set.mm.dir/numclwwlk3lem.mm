include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cclwwlknon.mm"
include "co.mm"
include "chash.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cmin.mm"
include "wne.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "caddc.mm"
include "cun.mm"
include "clwwlknon.mm"
include "a1i.mm"
include "fveq2d.mm"
include "wo.mm"
include "wb.mm"
include "wn.mm"
include "pm4.42.mm"
include "nne.mm"
include "anbi2i.mm"
include "orbi2i.mm"
include "bitri.mm"
include "rabbidv.mm"
include "unrab.mm"
include "syl6eqr.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "cvtx.mm"
include "fusgrvtxfi.mm"
include "ad2antrr.mm"
include "syl5eqelr.mm"
include "clwwlknfi.mm"
include "syl.mm"
include "rabfi.mm"
include "inrab.mm"
include "wral.mm"
include "neneq.mm"
include "adantl.mm"
include "intnand.mm"
include "imori.mm"
include "ianor.mm"
include "mpbir.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "hashun.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "cn.mm"
include "simpr.mm"
include "eluz2nn.mm"
include "numclwwlkovh.mm"
include "syl2an.mm"
include "numclwwlkovg.mm"
include "adantll.mm"
include "oveq12d.mm"
include "eqtr4d.mm"

theorem numclwwlk3lem
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let cQ: class Q
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
  let cK: class K
  let vi: setvar i
  let cW: class W
  let vh: setvar h
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )
  assume numclwwlk.h: |- H = ( v e. V , n e. NN |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) =/= ( w ` 0 ) ) } )
  assume numclwwlk.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V v
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint V w
  disjoint G f
  disjoint f w
  disjoint K w
  disjoint N f
  disjoint V f
  disjoint X f
  disjoint G i
  disjoint N i
  disjoint W i
  disjoint W v
  disjoint W w
  disjoint G h
  disjoint h w
  disjoint H h
  disjoint N h
  disjoint Q h
  disjoint V h
  disjoint h v
  disjoint X h
  assert |- ( ( ( G e. FinUSGraph /\ X e. V ) /\ N e. ( ZZ>= ` 2 ) ) -> ( # ` ( X ( ClWWalksNOn ` G ) N ) ) = ( ( # ` ( X H N ) ) + ( # ` ( X C N ) ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wa
    #
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    #
    chash
    cfv
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    cN
    c2
    cmin
    co
    @7
    cfv
    #
    @8
    wne
    #
    wa
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    chash
    cfv
    #
    @9
    @10
    @8
    wceq
    #
    wa
    #
    vw
    @13
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    cX
    cN
    cH
    co
    #
    chash
    cfv
    #
    cX
    cN
    cC
    co
    #
    chash
    cfv
    #
    caddc
    co
    @4
    @6
    @9
    vw
    @13
    crab
    #
    chash
    cfv
    @14
    @18
    cun
    #
    chash
    cfv
    #
    @20
    @4
    @5
    @25
    chash
    @5
    @25
    wceq
    @4
    vw
    cG
    cN
    cX
    clwwlknon
    a1i
    fveq2d
    @4
    @25
    @26
    chash
    @4
    @25
    @12
    @17
    wo
    #
    vw
    @13
    crab
    @26
    @4
    @9
    @28
    vw
    @13
    @9
    @28
    wb
    @4
    @9
    @12
    @9
    @11
    wn
    #
    wa
    #
    wo
    @28
    @9
    @11
    pm4.42
    @30
    @17
    @12
    @29
    @16
    @9
    @10
    @8
    nne
    anbi2i
    orbi2i
    bitri
    a1i
    rabbidv
    @12
    @17
    vw
    @13
    unrab
    syl6eqr
    fveq2d
    @4
    @14
    cfn
    wcel
    #
    @18
    cfn
    wcel
    #
    @14
    @18
    cin
    #
    c0
    wceq
    @27
    @20
    wceq
    @4
    @13
    cfn
    wcel
    #
    @31
    @4
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    @34
    @4
    @35
    cV
    cfn
    numclwwlk.v
    @0
    cV
    cfn
    wcel
    @1
    @3
    cG
    cV
    numclwwlk.v
    fusgrvtxfi
    ad2antrr
    syl5eqelr
    cG
    cN
    clwwlknfi
    syl
    #
    @12
    vw
    @13
    rabfi
    syl
    @4
    @34
    @32
    @36
    @17
    vw
    @13
    rabfi
    syl
    @4
    @33
    @12
    @17
    wa
    #
    vw
    @13
    crab
    #
    c0
    @12
    @17
    vw
    @13
    inrab
    @4
    @37
    wn
    #
    vw
    @13
    wral
    @38
    c0
    wceq
    @4
    @39
    vw
    @13
    @39
    @4
    @7
    @13
    wcel
    wa
    @39
    @12
    wn
    @17
    wn
    #
    wo
    @12
    @40
    @12
    @16
    @9
    @11
    @16
    wn
    @9
    @10
    @8
    neneq
    adantl
    intnand
    imori
    @12
    @17
    ianor
    mpbir
    a1i
    ralrimiva
    @37
    vw
    @13
    rabeq0
    sylibr
    syl5eq
    @14
    @18
    hashun
    syl3anc
    3eqtrd
    @4
    @22
    @15
    @24
    @19
    caddc
    @4
    @21
    @14
    chash
    @2
    @1
    cN
    cn
    wcel
    @21
    @14
    wceq
    @3
    @0
    @1
    simpr
    cN
    eluz2nn
    vw
    vv
    cQ
    vn
    cG
    cH
    cN
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlkovh
    syl2an
    fveq2d
    @4
    @23
    @18
    chash
    @1
    @3
    @23
    @18
    wceq
    @0
    vw
    vv
    cC
    vn
    cG
    cN
    cV
    cX
    numclwwlk.c
    numclwwlkovg
    adantll
    fveq2d
    oveq12d
    eqtr4d
end
