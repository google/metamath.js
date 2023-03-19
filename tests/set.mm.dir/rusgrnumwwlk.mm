include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "crusgr.mm"
include "wbr.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cuspgr.mm"
include "cusgr.mm"
include "rusgrusgr.mm"
include "usgruspgr.mm"
include "syl.mm"
include "simpr.mm"
include "rusgrnumwwlkb0.mm"
include "syl2anr.mm"
include "cfusgr.mm"
include "c0.mm"
include "wne.mm"
include "cc.mm"
include "simpl.mm"
include "anim12ci.mm"
include "isfusgr.mm"
include "sylibr.mm"
include "ne0i.mm"
include "ad2antlr.mm"
include "frusgrnn0.mm"
include "nn0cnd.mm"
include "syl3anc.mm"
include "exp0d.mm"
include "eqtr4d.mm"
include "anim1i.mm"
include "df-3an.mm"
include "rusgrnumwwlks.mm"
include "syl2an2r.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expd.mm"
include "com12.mm"
include "3impia.mm"
include "impcom.mm"

theorem rusgrnumwwlk
  let vw: setvar w
  let vv: setvar v
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  assume rusgrnumwwlk.v: |- V = ( Vtx ` G )
  assume rusgrnumwwlk.l: |- L = ( v e. V , n e. NN0 |-> ( # ` { w e. ( n WWalksN G ) | ( w ` 0 ) = v } ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint P n
  disjoint P v
  disjoint P w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint K w
  disjoint G i
  disjoint i w
  disjoint N i
  disjoint G p
  disjoint G x
  disjoint G y
  disjoint i n
  disjoint i p
  disjoint i x
  disjoint i y
  disjoint n p
  disjoint n x
  disjoint n y
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint K p
  disjoint K y
  disjoint N x
  disjoint N y
  disjoint P x
  disjoint P y
  disjoint V p
  disjoint V y
  disjoint K x
  disjoint L x
  disjoint L y
  disjoint V x
  disjoint v x
  disjoint v y
  assert |- ( ( G RegUSGraph K /\ ( V e. Fin /\ P e. V /\ N e. NN0 ) ) -> ( P L N ) = ( K ^ N ) )

  proof
    cV
    cfn
    wcel
    #
    cP
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    cG
    cK
    crusgr
    wbr
    #
    cP
    cN
    cL
    co
    #
    cK
    cN
    cexp
    co
    #
    wceq
    #
    @0
    @1
    @2
    @3
    @6
    wi
    #
    @2
    @0
    @1
    wa
    #
    @7
    @2
    @8
    @3
    @6
    @8
    @3
    wa
    #
    cP
    vx
    cv
    #
    cL
    co
    #
    cK
    @10
    cexp
    co
    #
    wceq
    #
    wi
    @9
    cP
    cc0
    cL
    co
    #
    cK
    cc0
    cexp
    co
    #
    wceq
    #
    wi
    @9
    cP
    vy
    cv
    #
    cL
    co
    #
    cK
    @17
    cexp
    co
    #
    wceq
    #
    wi
    @9
    cP
    @17
    c1
    caddc
    co
    #
    cL
    co
    #
    cK
    @21
    cexp
    co
    #
    wceq
    #
    wi
    @9
    @6
    wi
    vx
    vy
    cN
    @10
    cc0
    wceq
    #
    @13
    @16
    @9
    @25
    @11
    @14
    @12
    @15
    @10
    cc0
    cP
    cL
    oveq2
    @10
    cc0
    cK
    cexp
    oveq2
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @13
    @20
    @9
    @26
    @11
    @18
    @12
    @19
    @10
    @17
    cP
    cL
    oveq2
    @10
    @17
    cK
    cexp
    oveq2
    eqeq12d
    imbi2d
    @10
    @21
    wceq
    #
    @13
    @24
    @9
    @27
    @11
    @22
    @12
    @23
    @10
    @21
    cP
    cL
    oveq2
    @10
    @21
    cK
    cexp
    oveq2
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @13
    @6
    @9
    @28
    @11
    @4
    @12
    @5
    @10
    cN
    cP
    cL
    oveq2
    @10
    cN
    cK
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    @14
    c1
    @15
    @3
    cG
    cuspgr
    wcel
    #
    @1
    @14
    c1
    wceq
    @8
    @3
    cG
    cusgr
    wcel
    #
    @29
    cG
    cK
    rusgrusgr
    #
    cG
    usgruspgr
    syl
    @0
    @1
    simpr
    vw
    vv
    cP
    vn
    cG
    cL
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlkb0
    syl2anr
    @9
    cK
    @9
    cG
    cfusgr
    wcel
    #
    @3
    cV
    c0
    wne
    #
    cK
    cc
    wcel
    @9
    @30
    @0
    wa
    @32
    @8
    @0
    @3
    @30
    @0
    @1
    simpl
    @31
    anim12ci
    cG
    cV
    rusgrnumwwlk.v
    isfusgr
    sylibr
    @8
    @3
    simpr
    #
    @1
    @33
    @0
    @3
    cV
    cP
    ne0i
    ad2antlr
    @32
    @3
    @33
    w3a
    cK
    cG
    cK
    cV
    rusgrnumwwlk.v
    frusgrnn0
    nn0cnd
    syl3anc
    exp0d
    eqtr4d
    @17
    cn0
    wcel
    #
    @9
    @20
    @24
    @9
    @35
    @20
    @24
    wi
    #
    @9
    @3
    @35
    @0
    @1
    @35
    w3a
    #
    @36
    @34
    @9
    @35
    wa
    @8
    @35
    wa
    @37
    @9
    @8
    @35
    @8
    @3
    simpl
    anim1i
    @0
    @1
    @35
    df-3an
    sylibr
    vw
    vv
    cP
    vn
    cG
    cK
    cL
    @17
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlks
    syl2an2r
    expcom
    a2d
    nn0ind
    expd
    com12
    3impia
    impcom
end
