include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "csn.mm"
include "cdif.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "cc.mm"
include "cmul.mm"
include "1cnd.mm"
include "0le0.mm"
include "simpl.mm"
include "recnd.mm"
include "mul01d.mm"
include "syl5breqr.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "abs00bd.mm"
include "fveq2.mm"
include "abs1.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "cun.mm"
include "crab.mm"
include "w3a.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "wi.mm"
include "clt.mm"
include "simprll.mm"
include "0cn.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "sylancl.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "simprlr.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "abscld.mm"
include "simpll.mm"
include "1re.mm"
include "resubcl.mm"
include "remulcld.mm"
include "lenltd.mm"
include "mpbid.mm"
include "adantr.mm"
include "simprr.mm"
include "necomd.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "absgt0.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "syl5eqr.mm"
include "breq1d.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "1red.mm"
include "caddc.mm"
include "oveq2i.mm"
include "abs2dif.mm"
include "syl5eqbrr.mm"
include "abssub.mm"
include "breqtrd.mm"
include "letrd.mm"
include "lesubaddd.mm"
include "addsubd.mm"
include "subdid.mm"
include "mulid1d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "peano2re.mm"
include "leaddsub2d.mm"
include "adddird.mm"
include "mulid2d.mm"
include "3brtr4d.mm"
include "0red.mm"
include "simplr.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "leltned.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "crp.mm"
include "1rp.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "elbl3.mm"
include "mpanl12.mm"
include "expr.mm"
include "3impb.mm"
include "syl5bi.mm"
include "orrd.mm"
include "elun.mm"
include "sylibr.mm"
include "rabssdv.mm"
include "syl5eqss.mm"
include "ssundif.mm"
include "sylib.mm"
include "jca.mm"
include "syl2anc.mm"

theorem abelthlem2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vr: setvar r
  let cX: class X
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  let cF: class F
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }

  disjoint M z
  disjoint A z
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint M k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint M n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint n r
  disjoint X n
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
  disjoint A k
  disjoint m r
  disjoint m t
  disjoint m v
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint A n
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint S w
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( 1 e. S /\ ( S \ { 1 } ) C_ ( 0 ( ball ` ( abs o. - ) ) 1 ) ) )

  proof
    wph
    cM
    cr
    wcel
    #
    cc0
    cM
    cle
    wbr
    #
    c1
    cS
    wcel
    #
    cS
    c1
    csn
    #
    cdif
    cc0
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    wss
    #
    wa
    abelth.3
    abelth.4
    @0
    @1
    wa
    #
    @2
    @6
    @7
    c1
    cc
    wcel
    #
    cc0
    cM
    cc0
    cmul
    co
    #
    cle
    wbr
    #
    @2
    @7
    1cnd
    @7
    cc0
    cc0
    @9
    cle
    0le0
    @7
    cM
    @7
    cM
    @0
    @1
    simpl
    recnd
    #
    mul01d
    #
    syl5breqr
    c1
    vz
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cM
    c1
    @13
    cabs
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    @10
    vz
    c1
    cc
    cS
    @13
    c1
    wceq
    #
    @15
    cc0
    @18
    @9
    cle
    @20
    @14
    @20
    @14
    c1
    c1
    cmin
    co
    #
    cc0
    @13
    c1
    c1
    cmin
    oveq2
    1m1e0
    syl6eq
    abs00bd
    @20
    @17
    cc0
    cM
    cmul
    @20
    @17
    @21
    cc0
    @20
    @16
    c1
    c1
    cmin
    @20
    @16
    c1
    cabs
    cfv
    #
    c1
    @13
    c1
    cabs
    fveq2
    abs1
    syl6eq
    oveq2d
    1m1e0
    syl6eq
    oveq2d
    breq12d
    abelth.5
    elrab2
    sylanbrc
    @7
    cS
    @3
    @5
    cun
    #
    wss
    @6
    @7
    cS
    @19
    vz
    cc
    crab
    @23
    abelth.5
    @7
    @19
    vz
    cc
    @23
    @7
    @13
    cc
    wcel
    #
    @19
    w3a
    #
    @13
    @3
    wcel
    #
    @13
    @5
    wcel
    #
    wo
    @13
    @23
    wcel
    @25
    @26
    @27
    @26
    wn
    @13
    c1
    wne
    #
    @25
    @27
    @26
    @13
    c1
    vz
    c1
    velsn
    necon3bbii
    @7
    @24
    @19
    @28
    @27
    wi
    @7
    @24
    @19
    wa
    #
    @28
    @27
    @7
    @29
    @28
    wa
    #
    wa
    #
    @27
    @13
    cc0
    @4
    co
    #
    c1
    clt
    wbr
    #
    @31
    @32
    @16
    c1
    clt
    @31
    @32
    @13
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    @31
    @24
    cc0
    cc
    wcel
    #
    @32
    @35
    wceq
    @7
    @24
    @19
    @28
    simprll
    #
    0cn
    @13
    cc0
    @4
    @4
    eqid
    cnmetdval
    sylancl
    @31
    @34
    @13
    cabs
    @31
    @13
    @37
    subid1d
    fveq2d
    eqtrd
    @31
    @16
    c1
    clt
    wbr
    c1
    @16
    wne
    #
    @31
    @18
    @15
    clt
    wbr
    #
    wn
    #
    @38
    @31
    @19
    @40
    @7
    @24
    @19
    @28
    simprlr
    #
    @31
    @15
    @18
    @31
    @14
    @31
    @8
    @24
    @14
    cc
    wcel
    #
    ax-1cn
    @37
    c1
    @13
    subcl
    sylancr
    #
    abscld
    #
    @31
    cM
    @17
    @0
    @1
    @30
    simpll
    #
    @31
    c1
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @17
    cr
    wcel
    1re
    @31
    @13
    @37
    abscld
    #
    c1
    @16
    resubcl
    sylancr
    remulcld
    #
    lenltd
    mpbid
    @31
    @39
    c1
    @16
    @31
    @9
    @15
    clt
    wbr
    c1
    @16
    wceq
    #
    @39
    @31
    @9
    cc0
    @15
    clt
    @7
    @9
    cc0
    wceq
    @30
    @12
    adantr
    @31
    @14
    cc0
    wne
    #
    cc0
    @15
    clt
    wbr
    #
    @31
    @51
    c1
    @13
    wne
    #
    @31
    @13
    c1
    @7
    @29
    @28
    simprr
    necomd
    @31
    @8
    @24
    @51
    @53
    wb
    ax-1cn
    @37
    @8
    @24
    wa
    @14
    cc0
    c1
    @13
    c1
    @13
    subeq0
    necon3bid
    sylancr
    mpbird
    @31
    @42
    @51
    @52
    wb
    @43
    @14
    absgt0
    syl
    mpbid
    eqbrtrd
    @50
    @9
    @18
    @15
    clt
    @50
    cc0
    @17
    cM
    cmul
    @50
    cc0
    @21
    @17
    1m1e0
    c1
    @16
    c1
    cmin
    oveq2
    syl5eqr
    oveq2d
    breq1d
    syl5ibcom
    necon3bd
    mpd
    @31
    @16
    c1
    @48
    @31
    1red
    #
    @31
    @16
    c1
    cle
    wbr
    #
    cM
    c1
    caddc
    co
    #
    @16
    cmul
    co
    #
    @56
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @31
    cM
    @16
    cmul
    co
    #
    @16
    caddc
    co
    #
    @56
    @57
    @58
    cle
    @31
    @61
    @56
    cle
    wbr
    @16
    @56
    @60
    cmin
    co
    #
    cle
    wbr
    @31
    @16
    @18
    c1
    caddc
    co
    #
    @62
    cle
    @31
    @16
    c1
    cmin
    co
    #
    @18
    cle
    wbr
    @16
    @63
    cle
    wbr
    @31
    @64
    @15
    @18
    @31
    @47
    @46
    @64
    cr
    wcel
    @48
    1re
    @16
    c1
    resubcl
    sylancl
    @44
    @49
    @31
    @64
    @13
    c1
    cmin
    co
    cabs
    cfv
    #
    @15
    cle
    @31
    @64
    @16
    @22
    cmin
    co
    #
    @65
    cle
    @22
    c1
    @16
    cmin
    abs1
    oveq2i
    @31
    @24
    @8
    @66
    @65
    cle
    wbr
    @37
    ax-1cn
    @13
    c1
    abs2dif
    sylancl
    syl5eqbrr
    @31
    @24
    @8
    @65
    @15
    wceq
    @37
    ax-1cn
    @13
    c1
    abssub
    sylancl
    breqtrd
    @41
    letrd
    @31
    @16
    c1
    @18
    @48
    @54
    @49
    lesubaddd
    mpbid
    @31
    @62
    cM
    @60
    cmin
    co
    #
    c1
    caddc
    co
    @63
    @31
    cM
    c1
    @60
    @7
    cM
    cc
    wcel
    @30
    @11
    adantr
    #
    @31
    1cnd
    #
    @31
    @60
    @31
    cM
    @16
    @45
    @48
    remulcld
    #
    recnd
    addsubd
    @31
    @18
    @67
    c1
    caddc
    @31
    @18
    cM
    c1
    cmul
    co
    #
    @60
    cmin
    co
    @67
    @31
    cM
    c1
    @16
    @68
    @69
    @31
    @16
    @48
    recnd
    #
    subdid
    @31
    @71
    cM
    @60
    cmin
    @31
    cM
    @68
    mulid1d
    oveq1d
    eqtrd
    oveq1d
    eqtr4d
    breqtrrd
    @31
    @60
    @16
    @56
    @70
    @48
    @31
    @0
    @56
    cr
    wcel
    #
    @45
    cM
    peano2re
    syl
    #
    leaddsub2d
    mpbird
    @31
    @57
    @60
    c1
    @16
    cmul
    co
    #
    caddc
    co
    @61
    @31
    cM
    c1
    @16
    @68
    @69
    @72
    adddird
    @31
    @75
    @16
    @60
    caddc
    @31
    @16
    @72
    mulid2d
    oveq2d
    eqtrd
    @31
    @56
    @31
    @56
    @74
    recnd
    mulid1d
    3brtr4d
    @31
    @47
    @46
    @73
    cc0
    @56
    clt
    wbr
    @55
    @59
    wb
    @48
    @54
    @74
    @31
    cc0
    cM
    @56
    @31
    0red
    @45
    @74
    @0
    @1
    @30
    simplr
    @31
    cM
    @45
    ltp1d
    lelttrd
    @16
    c1
    @56
    lemul2
    syl112anc
    mpbird
    leltned
    mpbird
    eqbrtrd
    @31
    @36
    @24
    @27
    @33
    wb
    #
    0cn
    @37
    @4
    cc
    cxmt
    cfv
    wcel
    c1
    cxr
    wcel
    #
    @36
    @24
    wa
    @76
    cnxmet
    c1
    crp
    wcel
    @77
    1rp
    c1
    rpxr
    ax-mp
    @13
    @4
    cc0
    c1
    cc
    elbl3
    mpanl12
    sylancr
    mpbird
    expr
    3impb
    syl5bi
    orrd
    @13
    @3
    @5
    elun
    sylibr
    rabssdv
    syl5eqss
    cS
    @3
    @5
    ssundif
    sylib
    jca
    syl2anc
end
