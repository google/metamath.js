include "cfn.mm"
include "wcel.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wi.mm"
include "hashcl.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-clel.mm"
include "wal.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "2albidv.mm"
include "gen2.mm"
include "breq12.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "adantr.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "cbval2v.mm"
include "clt.mm"
include "nn0re.mm"
include "cr.mm"
include "1re.mm"
include "a1i.mm"
include "nn0ge0.mm"
include "0lt1.mm"
include "addgegt0d.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "adantrl.mm"
include "cvv.mm"
include "vex.mm"
include "hashgt0elex.mm"
include "csn.mm"
include "cdif.mm"
include "simpl.mm"
include "brfi1indlem.mm"
include "syl3anc.mm"
include "imp.mm"
include "w3a.mm"
include "peano2nn0.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "simplrr.mm"
include "simprlr.mm"
include "3jca.mm"
include "jca.mm"
include "difexg.mm"
include "ax-mp.mm"
include "spc2gv.mm"
include "mp2an.mm"
include "expdimp.mm"
include "syl6an.mm"
include "exp41.mm"
include "com15.mm"
include "com23.mm"
include "mpcom.mm"
include "ex.mm"
include "mpd.mm"
include "com4l.mm"
include "exlimiv.mm"
include "syl.mm"
include "com25.mm"
include "impcom.mm"
include "impancom.mm"
include "alrimivv.mm"
include "syl5bi.mm"
include "nn0ind.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "expd.mm"
include "syl5.mm"
include "expcom.mm"
include "eqcoms.mm"
include "sylbi.mm"

theorem brfi1indALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume brfi1ind.r: |- Rel G
  assume brfi1ind.f: |- F e. _V
  assume brfi1ind.1: |- ( ( v = V /\ e = E ) -> ( ps <-> ph ) )
  assume brfi1ind.2: |- ( ( v = w /\ e = f ) -> ( ps <-> th ) )
  assume brfi1ind.3: |- ( ( v G e /\ n e. v ) -> ( v \ { n } ) G F )
  assume brfi1ind.4: |- ( ( w = ( v \ { n } ) /\ f = F ) -> ( th <-> ch ) )
  assume brfi1ind.base: |- ( ( v G e /\ ( # ` v ) = 0 ) -> ps )
  assume brfi1ind.step: |- ( ( ( ( y + 1 ) e. NN0 /\ ( v G e /\ ( # ` v ) = ( y + 1 ) /\ n e. v ) ) /\ ch ) -> ps )

  disjoint E e
  disjoint E n
  disjoint E v
  disjoint e n
  disjoint e v
  disjoint n v
  disjoint F f
  disjoint F w
  disjoint f w
  disjoint G e
  disjoint G f
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint e f
  disjoint e w
  disjoint e y
  disjoint f n
  disjoint f v
  disjoint f y
  disjoint n w
  disjoint n y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint V e
  disjoint V n
  disjoint V v
  disjoint f ps
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint e th
  disjoint n th
  disjoint th v
  disjoint ch f
  disjoint ch w
  disjoint e ph
  disjoint n ph
  disjoint ph v
  disjoint e x
  disjoint n x
  disjoint v x
  disjoint x y
  disjoint G x
  disjoint ps x
  assert |- ( ( V G E /\ V e. Fin ) -> ph )

  proof
    cV
    cfn
    wcel
    #
    cV
    cE
    cG
    wbr
    #
    wph
    @0
    cV
    chash
    cfv
    #
    cn0
    wcel
    #
    @1
    wph
    wi
    #
    cV
    hashcl
    @3
    vn
    cv
    #
    @2
    wceq
    #
    @5
    cn0
    wcel
    #
    wa
    #
    vn
    wex
    @4
    vn
    @2
    cn0
    df-clel
    @8
    @4
    vn
    @6
    @7
    @4
    @7
    @4
    wi
    @2
    @5
    @2
    @5
    wceq
    #
    @1
    @7
    wph
    @1
    @9
    @7
    wph
    wi
    @7
    vv
    cv
    #
    ve
    cv
    #
    cG
    wbr
    #
    @10
    chash
    cfv
    #
    @5
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @1
    @9
    wa
    #
    wph
    @12
    @13
    vx
    cv
    #
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    @12
    @13
    cc0
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    @12
    @13
    vy
    cv
    #
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @12
    @13
    @26
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    wps
    wi
    #
    ve
    wal
    vv
    wal
    #
    @17
    vx
    vy
    @5
    @19
    cc0
    wceq
    #
    @22
    @25
    vv
    ve
    @36
    @21
    @24
    wps
    @36
    @20
    @23
    @12
    @19
    cc0
    @13
    eqeq2
    anbi2d
    imbi1d
    2albidv
    @19
    @26
    wceq
    #
    @22
    @29
    vv
    ve
    @37
    @21
    @28
    wps
    @37
    @20
    @27
    @12
    @19
    @26
    @13
    eqeq2
    anbi2d
    imbi1d
    2albidv
    @19
    @31
    wceq
    #
    @22
    @34
    vv
    ve
    @38
    @21
    @33
    wps
    @38
    @20
    @32
    @12
    @19
    @31
    @13
    eqeq2
    anbi2d
    imbi1d
    2albidv
    @19
    @5
    wceq
    #
    @22
    @16
    vv
    ve
    @39
    @21
    @15
    wps
    @39
    @20
    @14
    @12
    @19
    @5
    @13
    eqeq2
    anbi2d
    imbi1d
    2albidv
    @25
    vv
    ve
    brfi1ind.base
    gen2
    @30
    vw
    cv
    #
    vf
    cv
    #
    cG
    wbr
    #
    @40
    chash
    cfv
    #
    @26
    wceq
    #
    wa
    #
    wth
    wi
    #
    vf
    wal
    vw
    wal
    #
    @26
    cn0
    wcel
    #
    @35
    @29
    @46
    vv
    ve
    vw
    vf
    @10
    @40
    wceq
    #
    @11
    @41
    wceq
    #
    wa
    #
    @28
    @45
    wps
    wth
    @51
    @12
    @42
    @27
    @44
    @10
    @40
    @11
    @41
    cG
    breq12
    @49
    @27
    @44
    wb
    @50
    @49
    @13
    @43
    @26
    @10
    @40
    chash
    fveq2
    eqeq1d
    adantr
    anbi12d
    brfi1ind.2
    imbi12d
    cbval2v
    @48
    @47
    @35
    @48
    @47
    wa
    @34
    vv
    ve
    @48
    @33
    @47
    wps
    @48
    @33
    wa
    cc0
    @13
    clt
    wbr
    #
    @47
    wps
    wi
    #
    @48
    @32
    @52
    @12
    @48
    @32
    wa
    cc0
    @31
    @13
    clt
    @48
    cc0
    @31
    clt
    wbr
    @32
    @48
    @26
    c1
    @26
    nn0re
    c1
    cr
    wcel
    @48
    1re
    a1i
    @26
    nn0ge0
    cc0
    c1
    clt
    wbr
    @48
    0lt1
    a1i
    addgegt0d
    adantr
    @48
    @32
    simpr
    breqtrrd
    adantrl
    @33
    @48
    @52
    @53
    wi
    #
    @12
    @32
    @48
    @54
    wi
    #
    @10
    cvv
    wcel
    #
    @12
    @32
    @55
    wi
    wi
    vv
    vex
    #
    @56
    @52
    @32
    @48
    @12
    @53
    @56
    @52
    @32
    @48
    @12
    @53
    wi
    #
    wi
    wi
    #
    @56
    @52
    wa
    @5
    @10
    wcel
    #
    vn
    wex
    @59
    vn
    @10
    cvv
    hashgt0elex
    @60
    @59
    vn
    @12
    @60
    @32
    @48
    @53
    @12
    @60
    @32
    @48
    @53
    wi
    wi
    #
    @12
    @60
    wa
    @10
    @5
    csn
    #
    cdif
    #
    cF
    cG
    wbr
    #
    @61
    brfi1ind.3
    @12
    @60
    @64
    @61
    wi
    @48
    @60
    @64
    @32
    @12
    @53
    @48
    @60
    @64
    @32
    @58
    wi
    wi
    @48
    @60
    wa
    #
    @32
    @64
    @58
    @65
    @32
    @64
    @58
    wi
    #
    @63
    chash
    cfv
    #
    @26
    wceq
    #
    @65
    @32
    wa
    #
    @66
    @65
    @32
    @68
    @65
    @56
    @60
    @48
    @32
    @68
    wi
    @56
    @65
    @57
    a1i
    @48
    @60
    simpr
    @48
    @60
    simpl
    @5
    @10
    cvv
    @26
    brfi1indlem
    syl3anc
    imp
    @68
    @64
    @69
    @58
    @47
    @64
    @69
    @12
    @68
    wps
    @47
    @64
    @69
    @12
    @68
    wps
    wi
    @47
    @64
    wa
    #
    @69
    wa
    #
    @12
    wa
    #
    @31
    cn0
    wcel
    #
    @12
    @32
    @60
    w3a
    #
    wa
    @68
    wch
    wps
    @72
    @73
    @74
    @69
    @73
    @70
    @12
    @48
    @73
    @60
    @32
    @26
    peano2nn0
    ad2antrr
    ad2antlr
    @72
    @12
    @32
    @60
    @71
    @12
    simpr
    @70
    @65
    @32
    @12
    simplrr
    @71
    @60
    @12
    @70
    @48
    @60
    @32
    simprlr
    adantr
    3jca
    jca
    @70
    @68
    wch
    wi
    @69
    @12
    @47
    @64
    @68
    wch
    @63
    cvv
    wcel
    #
    cF
    cvv
    wcel
    @47
    @64
    @68
    wa
    #
    wch
    wi
    #
    wi
    @56
    @75
    @57
    @10
    @62
    cvv
    difexg
    ax-mp
    brfi1ind.f
    @46
    @77
    vw
    vf
    @63
    cF
    cvv
    cvv
    @40
    @63
    wceq
    #
    @41
    cF
    wceq
    #
    wa
    #
    @45
    @76
    wth
    wch
    @80
    @42
    @64
    @44
    @68
    @40
    @63
    @41
    cF
    cG
    breq12
    @78
    @44
    @68
    wb
    @79
    @78
    @43
    @67
    @26
    @40
    @63
    chash
    fveq2
    eqeq1d
    adantr
    anbi12d
    brfi1ind.4
    imbi12d
    spc2gv
    mp2an
    expdimp
    ad2antrr
    brfi1ind.step
    syl6an
    exp41
    com15
    com23
    mpcom
    ex
    com23
    ex
    com15
    imp
    mpd
    ex
    com4l
    exlimiv
    syl
    ex
    com25
    ax-mp
    imp
    impcom
    mpd
    impancom
    alrimivv
    ex
    syl5bi
    nn0ind
    @1
    @9
    @17
    wph
    wi
    #
    cV
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    wa
    #
    @1
    @9
    @81
    wi
    @1
    @82
    @83
    cV
    cE
    cG
    brfi1ind.r
    brrelexi
    cV
    cE
    cG
    brfi1ind.r
    brrelex2i
    jca
    @84
    @1
    @9
    @81
    @84
    @17
    @18
    wph
    @16
    @18
    wph
    wi
    vv
    ve
    cV
    cE
    cvv
    cvv
    @10
    cV
    wceq
    #
    @11
    cE
    wceq
    #
    wa
    #
    @15
    @18
    wps
    wph
    @87
    @12
    @1
    @14
    @9
    @10
    cV
    @11
    cE
    cG
    breq12
    @85
    @14
    @9
    wb
    @86
    @85
    @13
    @2
    @5
    @10
    cV
    chash
    fveq2
    eqeq1d
    adantr
    anbi12d
    brfi1ind.1
    imbi12d
    spc2gv
    com23
    expd
    mpcom
    imp
    syl5
    expcom
    com23
    eqcoms
    imp
    exlimiv
    sylbi
    syl
    impcom
end
