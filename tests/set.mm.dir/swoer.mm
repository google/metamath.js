include "wrel.mm"
include "cxp.mm"
include "wss.mm"
include "ccnv.mm"
include "cun.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "simpr.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "orcom.mm"
include "notbid.mm"
include "wcel.mm"
include "ssbri.mm"
include "adantl.mm"
include "brxp.mm"
include "sylib.mm"
include "brdifun.mm"
include "syl.mm"
include "simprd.mm"
include "simpld.mm"
include "syl2anc.mm"
include "3bitr4d.mm"
include "mpbid.mm"
include "simprl.mm"
include "ad2antrl.mm"
include "simplbi.mm"
include "simprbi.mm"
include "simprr.mm"
include "brel.mm"
include "wi.mm"
include "simpl.mm"
include "swopolem.mm"
include "syl13anc.mm"
include "syl6ibr.mm"
include "orim12d.mm"
include "or4.mm"
include "syl6ib.mm"
include "mtord.mm"
include "mpbird.mm"
include "wpo.mm"
include "swopo.mm"
include "poirr.mm"
include "sylan.mm"
include "pm1.2.mm"
include "nsyl.mm"
include "impbida.mm"
include "iserd.mm"

theorem swoer
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let c.lt: class .<
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cY: class Y
  assume swoer.1: |- R = ( ( X X. X ) \ ( .< u. `' .< ) )
  assume swoer.2: |- ( ( ph /\ ( y e. X /\ z e. X ) ) -> ( y .< z -> -. z .< y ) )
  assume swoer.3: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( x .< y -> ( x .< z \/ z .< y ) ) )

  disjoint x y
  disjoint x z
  disjoint .< x
  disjoint y z
  disjoint .< y
  disjoint .< z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint u v
  disjoint u w
  disjoint R u
  disjoint v w
  disjoint R v
  disjoint R w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint X u
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> R Er X )

  proof
    wph
    vu
    vv
    vw
    cX
    cR
    cR
    wrel
    #
    wph
    cR
    cX
    cX
    cxp
    #
    wss
    @1
    wrel
    @0
    cR
    @1
    c.lt
    c.lt
    ccnv
    cun
    #
    cdif
    @1
    swoer.1
    @1
    @2
    difss
    eqsstri
    #
    cX
    cX
    relxp
    cR
    @1
    relss
    mp2
    a1i
    wph
    vu
    cv
    #
    vv
    cv
    #
    cR
    wbr
    #
    wa
    #
    @6
    @5
    @4
    cR
    wbr
    #
    wph
    @6
    simpr
    @7
    @4
    @5
    c.lt
    wbr
    #
    @5
    @4
    c.lt
    wbr
    #
    wo
    #
    wn
    #
    @10
    @9
    wo
    #
    wn
    #
    @6
    @8
    @7
    @11
    @13
    @11
    @13
    wb
    @7
    @9
    @10
    orcom
    a1i
    notbid
    @7
    @4
    cX
    wcel
    #
    @5
    cX
    wcel
    #
    wa
    #
    @6
    @12
    wb
    #
    @7
    @4
    @5
    @1
    wbr
    #
    @17
    @6
    @19
    wph
    cR
    @1
    @4
    @5
    @3
    ssbri
    #
    adantl
    @4
    @5
    cX
    cX
    brxp
    #
    sylib
    #
    @4
    @5
    cR
    c.lt
    cX
    swoer.1
    brdifun
    #
    syl
    @7
    @16
    @15
    @8
    @14
    wb
    @7
    @15
    @16
    @22
    simprd
    @7
    @15
    @16
    @22
    simpld
    @5
    @4
    cR
    c.lt
    cX
    swoer.1
    brdifun
    syl2anc
    3bitr4d
    mpbid
    wph
    @6
    @5
    vw
    cv
    #
    cR
    wbr
    #
    wa
    #
    wa
    #
    @4
    @24
    cR
    wbr
    #
    @4
    @24
    c.lt
    wbr
    #
    @24
    @4
    c.lt
    wbr
    #
    wo
    #
    wn
    #
    @27
    @31
    @11
    @5
    @24
    c.lt
    wbr
    #
    @24
    @5
    c.lt
    wbr
    #
    wo
    #
    @27
    @6
    @12
    wph
    @6
    @25
    simprl
    @27
    @15
    @16
    @18
    @27
    @19
    @15
    @6
    @19
    wph
    @25
    @20
    ad2antrl
    #
    @19
    @15
    @16
    @21
    simplbi
    syl
    #
    @27
    @19
    @16
    @36
    @19
    @15
    @16
    @21
    simprbi
    syl
    #
    @23
    syl2anc
    mpbid
    @27
    @25
    @35
    wn
    #
    wph
    @6
    @25
    simprr
    #
    @27
    @16
    @24
    cX
    wcel
    #
    @25
    @39
    wb
    @38
    @27
    @25
    @41
    @40
    @25
    @16
    @41
    @5
    @24
    cX
    cX
    cR
    @3
    brel
    simprd
    syl
    #
    @5
    @24
    cR
    c.lt
    cX
    swoer.1
    brdifun
    syl2anc
    mpbid
    @27
    @31
    @9
    @33
    wo
    #
    @10
    @34
    wo
    #
    wo
    @11
    @35
    wo
    @27
    @29
    @43
    @30
    @44
    @27
    wph
    @15
    @41
    @16
    @29
    @43
    wi
    wph
    @26
    simpl
    #
    @37
    @42
    @38
    wph
    vx
    vy
    vz
    cX
    c.lt
    @4
    @24
    @5
    swoer.3
    swopolem
    syl13anc
    @27
    @30
    @34
    @10
    wo
    #
    @44
    @27
    wph
    @41
    @15
    @16
    @30
    @46
    wi
    @45
    @42
    @37
    @38
    wph
    vx
    vy
    vz
    cX
    c.lt
    @24
    @4
    @5
    swoer.3
    swopolem
    syl13anc
    @10
    @34
    orcom
    syl6ibr
    orim12d
    @9
    @33
    @10
    @34
    or4
    syl6ib
    mtord
    @27
    @15
    @41
    @28
    @32
    wb
    @37
    @42
    @4
    @24
    cR
    c.lt
    cX
    swoer.1
    brdifun
    syl2anc
    mpbird
    wph
    @15
    @4
    @4
    cR
    wbr
    #
    wph
    @15
    wa
    #
    @47
    @4
    @4
    c.lt
    wbr
    #
    @49
    wo
    #
    wn
    #
    @48
    @49
    @50
    wph
    cX
    c.lt
    wpo
    @15
    @49
    wn
    wph
    vx
    vy
    vz
    cX
    c.lt
    swoer.2
    swoer.3
    swopo
    cX
    @4
    c.lt
    poirr
    sylan
    @49
    pm1.2
    nsyl
    @48
    @15
    @15
    @47
    @51
    wb
    wph
    @15
    simpr
    #
    @52
    @4
    @4
    cR
    c.lt
    cX
    swoer.1
    brdifun
    syl2anc
    mpbird
    @47
    @15
    wph
    @47
    @4
    @4
    @1
    wbr
    #
    @15
    cR
    @1
    @4
    @4
    @3
    ssbri
    @53
    @15
    @15
    @4
    @4
    cX
    cX
    brxp
    simplbi
    syl
    adantl
    impbida
    iserd
end
