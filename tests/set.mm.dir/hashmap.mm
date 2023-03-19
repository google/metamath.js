include "cfn.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "c1.mm"
include "cc0.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "exp0d.mm"
include "eqcomd.mm"
include "c1o.mm"
include "cvv.mm"
include "vex.mm"
include "map0e.mm"
include "ax-mp.mm"
include "df1o2.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "0ex.mm"
include "hashsng.mm"
include "hash0.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "wa.mm"
include "cmul.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cin.mm"
include "snex.mm"
include "3pm3.2i.mm"
include "simprr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "mapunen.mm"
include "sylancr.mm"
include "wb.mm"
include "simpl.mm"
include "simprl.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "mapfi.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "xpfi.mm"
include "hashen.mm"
include "mpbird.mm"
include "hashxp.mm"
include "mapsnen.mm"
include "mpbiri.mm"
include "eqtrd.mm"
include "caddc.mm"
include "hashunsng.mm"
include "adantl.mm"
include "cc.mm"
include "adantr.mm"
include "cn0.mm"
include "ad2antrl.mm"
include "expp1d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "findcard2s.mm"
include "com12.mm"
include "vtoclga.mm"
include "imp.mm"

theorem hashmap
  let cA: class A
  let cB: class B
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( # ` ( A ^m B ) ) = ( ( # ` A ) ^ ( # ` B ) ) )

  proof
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    #
    cA
    cB
    cmap
    co
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    @0
    va
    cv
    #
    cB
    cmap
    co
    #
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    @4
    cexp
    co
    #
    wceq
    #
    wi
    @0
    @6
    wi
    va
    cA
    cfn
    @7
    cA
    wceq
    #
    @12
    @6
    @0
    @13
    @9
    @2
    @11
    @5
    @13
    @8
    @1
    chash
    @7
    cA
    cB
    cmap
    oveq1
    fveq2d
    @13
    @10
    @3
    @4
    cexp
    @7
    cA
    chash
    fveq2
    oveq1d
    eqeq12d
    imbi2d
    @0
    @7
    cfn
    wcel
    #
    @12
    @14
    @7
    vx
    cv
    #
    cmap
    co
    #
    chash
    cfv
    #
    @10
    @15
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wi
    @14
    @7
    c0
    cmap
    co
    #
    chash
    cfv
    #
    @10
    c0
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wi
    @14
    @7
    vy
    cv
    #
    cmap
    co
    #
    chash
    cfv
    #
    @10
    @26
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wi
    @14
    @7
    @26
    vz
    cv
    #
    csn
    #
    cun
    #
    cmap
    co
    #
    chash
    cfv
    #
    @10
    @34
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wi
    @14
    @12
    wi
    vx
    vy
    vz
    cB
    @15
    c0
    wceq
    #
    @20
    @25
    @14
    @40
    @17
    @22
    @19
    @24
    @40
    @16
    @21
    chash
    @15
    c0
    @7
    cmap
    oveq2
    fveq2d
    @40
    @18
    @23
    @10
    cexp
    @15
    c0
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @15
    @26
    wceq
    #
    @20
    @31
    @14
    @41
    @17
    @28
    @19
    @30
    @41
    @16
    @27
    chash
    @15
    @26
    @7
    cmap
    oveq2
    fveq2d
    @41
    @18
    @29
    @10
    cexp
    @15
    @26
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @15
    @34
    wceq
    #
    @20
    @39
    @14
    @42
    @17
    @36
    @19
    @38
    @42
    @16
    @35
    chash
    @15
    @34
    @7
    cmap
    oveq2
    fveq2d
    @42
    @18
    @37
    @10
    cexp
    @15
    @34
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @15
    cB
    wceq
    #
    @20
    @12
    @14
    @43
    @17
    @9
    @19
    @11
    @43
    @16
    @8
    chash
    @15
    cB
    @7
    cmap
    oveq2
    fveq2d
    @43
    @18
    @4
    @10
    cexp
    @15
    cB
    chash
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @14
    c1
    @10
    cc0
    cexp
    co
    #
    @22
    @24
    @14
    @44
    c1
    @14
    @10
    @14
    @10
    @7
    hashcl
    nn0cnd
    #
    exp0d
    eqcomd
    @22
    c0
    csn
    #
    chash
    cfv
    #
    c1
    @21
    @46
    chash
    @21
    c1o
    @46
    @7
    cvv
    wcel
    #
    @21
    c1o
    wceq
    va
    vex
    #
    @7
    cvv
    map0e
    ax-mp
    df1o2
    eqtri
    fveq2i
    c0
    cvv
    wcel
    @47
    c1
    wceq
    0ex
    c0
    cvv
    hashsng
    ax-mp
    eqtri
    @23
    cc0
    @10
    cexp
    hash0
    oveq2i
    3eqtr4g
    @26
    cfn
    wcel
    #
    @32
    @26
    wcel
    wn
    #
    wa
    #
    @14
    @31
    @39
    @14
    @52
    @31
    @39
    wi
    @31
    @39
    @14
    @52
    wa
    #
    @28
    @10
    cmul
    co
    #
    @30
    @10
    cmul
    co
    #
    wceq
    @28
    @30
    @10
    cmul
    oveq1
    @53
    @36
    @54
    @38
    @55
    @53
    @36
    @27
    @7
    @33
    cmap
    co
    #
    cxp
    #
    chash
    cfv
    #
    @54
    @53
    @36
    @58
    wceq
    #
    @35
    @57
    cen
    wbr
    #
    @53
    @26
    cvv
    wcel
    #
    @33
    cvv
    wcel
    #
    @48
    w3a
    @26
    @33
    cin
    c0
    wceq
    #
    @60
    @61
    @62
    @48
    vy
    vex
    @32
    snex
    @49
    3pm3.2i
    @53
    @51
    @63
    @14
    @50
    @51
    simprr
    @26
    @32
    disjsn
    sylibr
    @26
    @33
    @7
    cvv
    cvv
    cvv
    mapunen
    sylancr
    @53
    @35
    cfn
    wcel
    #
    @57
    cfn
    wcel
    #
    @59
    @60
    wb
    @53
    @14
    @34
    cfn
    wcel
    #
    @64
    @14
    @52
    simpl
    #
    @53
    @50
    @33
    cfn
    wcel
    #
    @66
    @14
    @50
    @51
    simprl
    @32
    snfi
    #
    @26
    @33
    unfi
    sylancl
    @7
    @34
    mapfi
    syl2anc
    @53
    @27
    cfn
    wcel
    #
    @56
    cfn
    wcel
    #
    @65
    @14
    @50
    @70
    @51
    @7
    @26
    mapfi
    adantrr
    #
    @53
    @14
    @68
    @71
    @67
    @69
    @7
    @33
    mapfi
    sylancl
    #
    @27
    @56
    xpfi
    syl2anc
    @35
    @57
    hashen
    syl2anc
    mpbird
    @53
    @58
    @28
    @56
    chash
    cfv
    #
    cmul
    co
    #
    @54
    @53
    @70
    @71
    @58
    @75
    wceq
    @72
    @73
    @27
    @56
    hashxp
    syl2anc
    @53
    @74
    @10
    @28
    cmul
    @53
    @74
    @10
    wceq
    #
    @56
    @7
    cen
    wbr
    #
    @7
    @32
    @49
    vz
    vex
    #
    mapsnen
    @53
    @71
    @14
    @76
    @77
    wb
    @73
    @67
    @56
    @7
    hashen
    syl2anc
    mpbiri
    oveq2d
    eqtrd
    eqtrd
    @53
    @38
    @10
    @29
    c1
    caddc
    co
    #
    cexp
    co
    @55
    @53
    @37
    @79
    @10
    cexp
    @52
    @37
    @79
    wceq
    #
    @14
    @32
    cvv
    wcel
    @52
    @80
    wi
    @78
    @26
    @32
    cvv
    hashunsng
    ax-mp
    adantl
    oveq2d
    @53
    @10
    @29
    @14
    @10
    cc
    wcel
    @52
    @45
    adantr
    @50
    @29
    cn0
    wcel
    @14
    @51
    @26
    hashcl
    ad2antrl
    expp1d
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    findcard2s
    com12
    vtoclga
    imp
end
