include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "ctp.mm"
include "wceq.mm"
include "cusgr.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "wreu.mm"
include "weu.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wo.mm"
include "animorr.mm"
include "wb.mm"
include "preq2.mm"
include "eleq1d.mm"
include "rexprg.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "df-rex.mm"
include "sylib.mm"
include "vex.mm"
include "elpr.mm"
include "eqidd.mm"
include "a1i.mm"
include "a1i13.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "3imtr4d.mm"
include "usgredgne.mm"
include "adantll.mm"
include "wn.mm"
include "df-ne.mm"
include "eqid.mm"
include "pm2.24i.mm"
include "sylbi.mm"
include "syl.mm"
include "ex.mm"
include "ad2antlr.mm"
include "com12.mm"
include "2a1i.mm"
include "jaoi.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "com3l.mm"
include "imp.mm"
include "imp31.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "eu4.mm"
include "sylanbrc.mm"
include "df-reu.mm"
include "sylibr.mm"

theorem 3vfriswmgrlem
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume 3vfriswmgr.v: |- V = ( Vtx ` G )
  assume 3vfriswmgr.e: |- E = ( Edg ` G )

  disjoint A w
  disjoint B w
  disjoint C w
  disjoint E w
  disjoint G w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint A y
  disjoint w y
  disjoint B y
  disjoint C y
  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y y
  assert |- ( ( ( A e. X /\ B e. Y /\ A =/= B ) /\ ( V = { A , B , C } /\ G e. USGraph ) ) -> ( { A , B } e. E -> E! w e. { A , B } { A , w } e. E ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cV
    cA
    cB
    cC
    ctp
    wceq
    #
    cG
    cusgr
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cA
    vw
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vw
    @8
    wreu
    #
    @7
    @9
    wa
    #
    @10
    @8
    wcel
    #
    @12
    wa
    #
    vw
    weu
    #
    @13
    @14
    @16
    vw
    wex
    #
    @16
    vy
    cv
    #
    @8
    wcel
    #
    cA
    @19
    cpr
    #
    cE
    wcel
    #
    wa
    #
    wa
    #
    @10
    @19
    wceq
    #
    wi
    #
    vy
    wal
    vw
    wal
    @17
    @14
    @12
    vw
    @8
    wrex
    #
    @18
    @14
    @27
    cA
    cA
    cpr
    #
    cE
    wcel
    #
    @9
    wo
    #
    @7
    @9
    @29
    animorr
    @3
    @27
    @30
    wb
    #
    @6
    @9
    @0
    @1
    @31
    @2
    @12
    @29
    @9
    vw
    cA
    cB
    cX
    cY
    @10
    cA
    wceq
    #
    @11
    @28
    cE
    @10
    cA
    cA
    preq2
    eleq1d
    #
    @10
    cB
    wceq
    #
    @11
    @8
    cE
    @10
    cB
    cA
    preq2
    eleq1d
    #
    rexprg
    3adant3
    ad2antrr
    mpbird
    @12
    vw
    @8
    df-rex
    sylib
    @14
    @26
    vw
    vy
    @24
    @14
    @25
    @15
    @12
    @23
    @14
    @25
    wi
    #
    @15
    @32
    @34
    wo
    #
    @12
    @23
    @36
    wi
    wi
    @10
    cA
    cB
    vw
    vex
    elpr
    @23
    @37
    @12
    @36
    @20
    @22
    @37
    @12
    @36
    wi
    #
    wi
    #
    @20
    @19
    cA
    wceq
    #
    @19
    cB
    wceq
    #
    wo
    #
    @22
    @39
    wi
    @19
    cA
    cB
    vy
    vex
    elpr
    @37
    @42
    @22
    @38
    @32
    @42
    @22
    @38
    wi
    #
    wi
    @34
    @42
    @43
    @32
    @22
    @29
    @14
    cA
    @19
    wceq
    #
    wi
    #
    wi
    #
    wi
    #
    @40
    @47
    @41
    @40
    @29
    @29
    @14
    cA
    cA
    wceq
    #
    wi
    #
    wi
    @22
    @46
    @40
    @29
    @29
    @49
    @49
    @29
    @14
    cA
    eqidd
    a1i
    a1i13
    @40
    @21
    @28
    cE
    @19
    cA
    cA
    preq2
    eleq1d
    #
    @40
    @45
    @49
    @29
    @40
    @44
    @48
    @14
    @19
    cA
    cA
    eqeq2
    imbi2d
    imbi2d
    3imtr4d
    @41
    @9
    @29
    @14
    cA
    cB
    wceq
    #
    wi
    #
    wi
    #
    @22
    @46
    @53
    @41
    @9
    @14
    @29
    @51
    @6
    @29
    @51
    wi
    @3
    @9
    @6
    @29
    @51
    @6
    @29
    wa
    #
    cA
    cA
    wne
    #
    @51
    @5
    @29
    @55
    @4
    cE
    cG
    cA
    cA
    3vfriswmgr.e
    usgredgne
    adantll
    #
    @55
    @48
    wn
    #
    @51
    cA
    cA
    df-ne
    #
    @48
    @51
    cA
    eqid
    #
    pm2.24i
    sylbi
    syl
    ex
    ad2antlr
    com12
    2a1i
    @41
    @21
    @8
    cE
    @19
    cB
    cA
    preq2
    eleq1d
    #
    @41
    @45
    @52
    @29
    @41
    @44
    @51
    @14
    @19
    cB
    cA
    eqeq2
    imbi2d
    imbi2d
    3imtr4d
    jaoi
    @32
    @38
    @46
    @22
    @32
    @12
    @29
    @36
    @45
    @33
    @32
    @25
    @44
    @14
    @10
    cA
    @19
    eqeq1
    imbi2d
    imbi12d
    imbi2d
    syl5ibr
    @42
    @43
    @34
    @22
    @9
    @14
    cB
    @19
    wceq
    #
    wi
    #
    wi
    #
    wi
    #
    @40
    @64
    @41
    @40
    @29
    @9
    @14
    cB
    cA
    wceq
    #
    wi
    #
    wi
    @22
    @63
    @40
    @29
    @9
    @66
    @14
    @29
    @65
    @6
    @29
    @65
    wi
    @3
    @9
    @6
    @29
    @65
    @54
    @55
    @65
    @56
    @55
    @57
    @65
    @58
    @48
    @65
    @59
    pm2.24i
    sylbi
    syl
    ex
    ad2antlr
    com12
    a1i13
    @50
    @40
    @62
    @66
    @9
    @40
    @61
    @65
    @14
    @19
    cA
    cB
    eqeq2
    imbi2d
    imbi2d
    3imtr4d
    @41
    @9
    @9
    @14
    cB
    cB
    wceq
    #
    wi
    #
    wi
    @22
    @63
    @41
    @9
    @9
    @68
    @68
    @9
    @14
    cB
    eqidd
    a1i
    a1i13
    @60
    @41
    @62
    @68
    @9
    @41
    @61
    @67
    @14
    @19
    cB
    cB
    eqeq2
    imbi2d
    imbi2d
    3imtr4d
    jaoi
    @34
    @38
    @63
    @22
    @34
    @12
    @9
    @36
    @62
    @35
    @34
    @25
    @61
    @14
    @10
    cB
    @19
    eqeq1
    imbi2d
    imbi12d
    imbi2d
    syl5ibr
    jaoi
    com3l
    sylbi
    imp
    com3l
    sylbi
    imp31
    com12
    alrimivv
    @16
    @23
    vw
    vy
    @25
    @15
    @20
    @12
    @22
    @10
    @19
    @8
    eleq1
    @25
    @11
    @21
    cE
    @10
    @19
    cA
    preq2
    eleq1d
    anbi12d
    eu4
    sylanbrc
    @12
    vw
    @8
    df-reu
    sylibr
    ex
end
