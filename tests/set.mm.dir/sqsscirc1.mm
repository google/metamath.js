include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "cexp.mm"
include "caddc.mm"
include "csqrt.mm"
include "cfv.mm"
include "simp-4l.mm"
include "resqcld.mm"
include "simpllr.mm"
include "simpld.mm"
include "readdcld.mm"
include "sqge0d.mm"
include "addge0d.mm"
include "resqrtcld.mm"
include "simplr.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "simprl.mm"
include "simp-4r.mm"
include "2rp.mm"
include "a1i.mm"
include "rpge0d.mm"
include "divge0d.mm"
include "lt2sqd.mm"
include "mpbid.mm"
include "simprr.mm"
include "simprd.mm"
include "lt2addd.mm"
include "sqrtltd.mm"
include "cmul.mm"
include "rpre.mm"
include "recnd.mm"
include "2timesd.mm"
include "fveq2d.mm"
include "rpge0.mm"
include "sqrtsqd.mm"
include "oveq2d.mm"
include "2re.mm"
include "0le2.mm"
include "sqrtmuld.mm"
include "2cnd.mm"
include "sqrtcld.mm"
include "rpcn.mm"
include "wne.mm"
include "2ne0.mm"
include "div32d.mm"
include "3eqtr4d.mm"
include "eqtr3d.mm"
include "c1.mm"
include "c4.mm"
include "2lt4.mm"
include "wb.mm"
include "4re.mm"
include "0re.mm"
include "4pos.mm"
include "ltleii.mm"
include "sqrtlt.mm"
include "mp4an.mm"
include "mpbi.mm"
include "2pos.mm"
include "sqrtpclii.mm"
include "ltdiv1ii.mm"
include "wceq.mm"
include "sqrtsq.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "sq2.mm"
include "fveq2i.mm"
include "2div2e1.mm"
include "3eqtr3i.mm"
include "breqtri.mm"
include "1red.mm"
include "id.mm"
include "ltmul1d.mm"
include "mpbii.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "syl.mm"
include "lttrd.mm"
include "ex.mm"

theorem sqsscirc1
  let cD: class D
  let cX: class X
  let cY: class Y


  assert |- ( ( ( ( X e. RR /\ 0 <_ X ) /\ ( Y e. RR /\ 0 <_ Y ) ) /\ D e. RR+ ) -> ( ( X < ( D / 2 ) /\ Y < ( D / 2 ) ) -> ( sqrt ` ( ( X ^ 2 ) + ( Y ^ 2 ) ) ) < D ) )

  proof
    cX
    cr
    wcel
    #
    cc0
    cX
    cle
    wbr
    #
    wa
    #
    cY
    cr
    wcel
    #
    cc0
    cY
    cle
    wbr
    #
    wa
    #
    wa
    #
    cD
    crp
    wcel
    #
    wa
    #
    cX
    cD
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cY
    @9
    clt
    wbr
    #
    wa
    #
    cX
    c2
    cexp
    co
    #
    cY
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    clt
    wbr
    @8
    @12
    wa
    #
    @16
    @9
    c2
    cexp
    co
    #
    @18
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    @17
    @15
    @17
    @13
    @14
    @17
    cX
    @0
    @1
    @5
    @7
    @12
    simp-4l
    #
    resqcld
    #
    @17
    cY
    @17
    @3
    @4
    @2
    @5
    @7
    @12
    simpllr
    #
    simpld
    #
    resqcld
    #
    readdcld
    #
    @17
    @13
    @14
    @22
    @25
    @17
    cX
    @21
    sqge0d
    @17
    cY
    @24
    sqge0d
    addge0d
    #
    resqrtcld
    @17
    @19
    @17
    @18
    @18
    @17
    @9
    @17
    cD
    @17
    cD
    @6
    @7
    @12
    simplr
    #
    rpred
    #
    rehalfcld
    #
    resqcld
    #
    @31
    readdcld
    #
    @17
    @18
    @18
    @31
    @31
    @17
    @9
    @30
    sqge0d
    #
    @33
    addge0d
    #
    resqrtcld
    @29
    @17
    @15
    @19
    clt
    wbr
    @16
    @20
    clt
    wbr
    @17
    @13
    @14
    @18
    @18
    @22
    @25
    @31
    @31
    @17
    @10
    @13
    @18
    clt
    wbr
    @8
    @10
    @11
    simprl
    @17
    cX
    @9
    @21
    @30
    @0
    @1
    @5
    @7
    @12
    simp-4r
    @17
    cD
    c2
    @29
    c2
    crp
    wcel
    #
    @17
    2rp
    a1i
    @17
    cD
    @28
    rpge0d
    divge0d
    #
    lt2sqd
    mpbid
    @17
    @11
    @14
    @18
    clt
    wbr
    @8
    @10
    @11
    simprr
    @17
    cY
    @9
    @24
    @30
    @17
    @3
    @4
    @23
    simprd
    @36
    lt2sqd
    mpbid
    lt2addd
    @17
    @15
    @19
    @26
    @27
    @32
    @34
    sqrtltd
    mpbid
    @17
    @7
    @20
    cD
    clt
    wbr
    @28
    @7
    @20
    c2
    csqrt
    cfv
    #
    c2
    cdiv
    co
    #
    cD
    cmul
    co
    #
    cD
    clt
    @7
    c2
    @18
    cmul
    co
    #
    csqrt
    cfv
    #
    @20
    @39
    @7
    @40
    @19
    csqrt
    @7
    @18
    @7
    @18
    @7
    @9
    @7
    cD
    cD
    rpre
    #
    rehalfcld
    #
    resqcld
    #
    recnd
    2timesd
    fveq2d
    @7
    @37
    @18
    csqrt
    cfv
    #
    cmul
    co
    @37
    @9
    cmul
    co
    @41
    @39
    @7
    @45
    @9
    @37
    cmul
    @7
    @9
    @43
    @7
    cD
    c2
    @42
    @35
    @7
    2rp
    a1i
    cD
    rpge0
    divge0d
    sqrtsqd
    oveq2d
    @7
    c2
    @18
    c2
    cr
    wcel
    #
    @7
    2re
    a1i
    #
    cc0
    c2
    cle
    wbr
    #
    @7
    0le2
    a1i
    #
    @44
    @7
    @9
    @43
    sqge0d
    sqrtmuld
    @7
    @37
    c2
    cD
    @7
    c2
    @7
    2cnd
    #
    sqrtcld
    @50
    cD
    rpcn
    #
    c2
    cc0
    wne
    @7
    2ne0
    a1i
    div32d
    3eqtr4d
    eqtr3d
    @7
    @39
    c1
    cD
    cmul
    co
    #
    cD
    clt
    @7
    @38
    c1
    clt
    wbr
    @39
    @52
    clt
    wbr
    @38
    c4
    csqrt
    cfv
    #
    c2
    cdiv
    co
    #
    c1
    clt
    @37
    @53
    clt
    wbr
    #
    @38
    @54
    clt
    wbr
    c2
    c4
    clt
    wbr
    #
    @55
    2lt4
    @46
    @48
    c4
    cr
    wcel
    cc0
    c4
    cle
    wbr
    @56
    @55
    wb
    2re
    0le2
    4re
    cc0
    c4
    0re
    4re
    4pos
    ltleii
    c2
    c4
    sqrtlt
    mp4an
    mpbi
    @37
    @53
    c2
    c2
    2re
    2pos
    sqrtpclii
    c4
    4re
    4pos
    sqrtpclii
    2re
    2pos
    ltdiv1ii
    mpbi
    c2
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c2
    cdiv
    co
    c2
    c2
    cdiv
    co
    @54
    c1
    @58
    c2
    c2
    cdiv
    @46
    @48
    @58
    c2
    wceq
    2re
    0le2
    c2
    sqrtsq
    mp2an
    oveq1i
    @58
    @53
    c2
    cdiv
    @57
    c4
    csqrt
    sq2
    fveq2i
    oveq1i
    2div2e1
    3eqtr3i
    breqtri
    @7
    @38
    c1
    cD
    @7
    @37
    @7
    c2
    @47
    @49
    resqrtcld
    rehalfcld
    @7
    1red
    @7
    id
    ltmul1d
    mpbii
    @7
    cD
    @51
    mulid2d
    breqtrd
    eqbrtrd
    syl
    lttrd
    ex
end
