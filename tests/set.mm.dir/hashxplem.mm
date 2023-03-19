include "cv.mm"
include "cxp.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "xpeq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "cc0.mm"
include "cfn.mm"
include "wcel.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "ax-mp.mm"
include "hash0.mm"
include "oveq1i.mm"
include "0xp.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "3eqtr4ri.mm"
include "wn.mm"
include "wa.mm"
include "caddc.mm"
include "oveq1.mm"
include "adantl.mm"
include "xpundir.mm"
include "cin.mm"
include "xpfi.mm"
include "mpan2.mm"
include "inxp.mm"
include "disjsn.mm"
include "biimpri.mm"
include "xpeq1d.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "snfi.mm"
include "mp2an.mm"
include "hashun.mm"
include "mp3an2.mm"
include "syl2an.mm"
include "cen.mm"
include "wbr.mm"
include "snex.mm"
include "elexi.mm"
include "xpcomen.mm"
include "vex.mm"
include "xpsnen.mm"
include "entri.mm"
include "wb.mm"
include "hashen.mm"
include "mpbir.mm"
include "oveq2i.mm"
include "adantr.mm"
include "c1.mm"
include "cvv.mm"
include "wi.mm"
include "hashunsng.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cn0.mm"
include "nn0cn.mm"
include "mp2b.mm"
include "adddir.mm"
include "mp3an23.mm"
include "syl.mm"
include "mulid2i.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "findcard2s.mm"

theorem hashxplem
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hashxplem.1: |- B e. Fin


  assert |- ( A e. Fin -> ( # ` ( A X. B ) ) = ( ( # ` A ) x. ( # ` B ) ) )

  proof
    vx
    cv
    #
    cB
    cxp
    #
    chash
    cfv
    #
    @0
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    c0
    cB
    cxp
    #
    chash
    cfv
    #
    c0
    chash
    cfv
    #
    @4
    cmul
    co
    #
    wceq
    vy
    cv
    #
    cB
    cxp
    #
    chash
    cfv
    #
    @10
    chash
    cfv
    #
    @4
    cmul
    co
    #
    wceq
    #
    @10
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    cxp
    #
    chash
    cfv
    #
    @18
    chash
    cfv
    #
    @4
    cmul
    co
    #
    wceq
    #
    cA
    cB
    cxp
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    @4
    cmul
    co
    #
    wceq
    vx
    vy
    vz
    cA
    @0
    c0
    wceq
    #
    @2
    @7
    @5
    @9
    @28
    @1
    @6
    chash
    @0
    c0
    cB
    xpeq1
    fveq2d
    @28
    @3
    @8
    @4
    cmul
    @0
    c0
    chash
    fveq2
    oveq1d
    eqeq12d
    @0
    @10
    wceq
    #
    @2
    @12
    @5
    @14
    @29
    @1
    @11
    chash
    @0
    @10
    cB
    xpeq1
    fveq2d
    @29
    @3
    @13
    @4
    cmul
    @0
    @10
    chash
    fveq2
    oveq1d
    eqeq12d
    @0
    @18
    wceq
    #
    @2
    @20
    @5
    @22
    @30
    @1
    @19
    chash
    @0
    @18
    cB
    xpeq1
    fveq2d
    @30
    @3
    @21
    @4
    cmul
    @0
    @18
    chash
    fveq2
    oveq1d
    eqeq12d
    @0
    cA
    wceq
    #
    @2
    @25
    @5
    @27
    @31
    @1
    @24
    chash
    @0
    cA
    cB
    xpeq1
    fveq2d
    @31
    @3
    @26
    @4
    cmul
    @0
    cA
    chash
    fveq2
    oveq1d
    eqeq12d
    cc0
    @4
    cmul
    co
    #
    cc0
    @9
    @7
    cB
    cfn
    wcel
    #
    @32
    cc0
    wceq
    hashxplem.1
    @33
    @4
    @33
    @4
    cB
    hashcl
    #
    nn0cnd
    mul02d
    ax-mp
    @8
    cc0
    @4
    cmul
    hash0
    oveq1i
    @7
    @8
    cc0
    @6
    c0
    chash
    cB
    0xp
    fveq2i
    hash0
    eqtri
    3eqtr4ri
    @10
    cfn
    wcel
    #
    @16
    @10
    wcel
    wn
    #
    wa
    #
    @15
    @23
    @37
    @15
    wa
    @12
    @4
    caddc
    co
    #
    @14
    @4
    caddc
    co
    #
    @20
    @22
    @15
    @38
    @39
    wceq
    @37
    @12
    @14
    @4
    caddc
    oveq1
    adantl
    @37
    @20
    @38
    wceq
    @15
    @37
    @20
    @11
    @17
    cB
    cxp
    #
    cun
    #
    chash
    cfv
    #
    @38
    @19
    @41
    chash
    @10
    @17
    cB
    xpundir
    fveq2i
    @37
    @42
    @12
    @40
    chash
    cfv
    #
    caddc
    co
    #
    @38
    @35
    @11
    cfn
    wcel
    #
    @11
    @40
    cin
    #
    c0
    wceq
    #
    @42
    @44
    wceq
    #
    @36
    @35
    @33
    @45
    hashxplem.1
    @10
    cB
    xpfi
    mpan2
    @36
    @46
    @10
    @17
    cin
    #
    cB
    cB
    cin
    #
    cxp
    #
    c0
    @10
    cB
    @17
    cB
    inxp
    @36
    @51
    c0
    @50
    cxp
    c0
    @36
    @49
    c0
    @50
    @49
    c0
    wceq
    @36
    @10
    @16
    disjsn
    biimpri
    xpeq1d
    @50
    0xp
    syl6eq
    syl5eq
    @45
    @40
    cfn
    wcel
    #
    @47
    @48
    @17
    cfn
    wcel
    @33
    @52
    @16
    snfi
    hashxplem.1
    @17
    cB
    xpfi
    mp2an
    #
    @11
    @40
    hashun
    mp3an2
    syl2an
    @43
    @4
    @12
    caddc
    @43
    @4
    wceq
    #
    @40
    cB
    cen
    wbr
    #
    @40
    cB
    @17
    cxp
    cB
    @17
    cB
    @16
    snex
    cB
    cfn
    hashxplem.1
    elexi
    #
    xpcomen
    cB
    @16
    @56
    vz
    vex
    #
    xpsnen
    entri
    @52
    @33
    @54
    @55
    wb
    @53
    hashxplem.1
    @40
    cB
    hashen
    mp2an
    mpbir
    oveq2i
    syl6eq
    syl5eq
    adantr
    @37
    @22
    @39
    wceq
    @15
    @37
    @22
    @13
    c1
    caddc
    co
    #
    @4
    cmul
    co
    #
    @39
    @37
    @21
    @58
    @4
    cmul
    @16
    cvv
    wcel
    @37
    @21
    @58
    wceq
    wi
    @57
    @10
    @16
    cvv
    hashunsng
    ax-mp
    oveq1d
    @35
    @59
    @39
    wceq
    @36
    @35
    @59
    @14
    c1
    @4
    cmul
    co
    #
    caddc
    co
    #
    @39
    @35
    @13
    cc
    wcel
    #
    @59
    @61
    wceq
    #
    @35
    @13
    @10
    hashcl
    nn0cnd
    @62
    c1
    cc
    wcel
    @4
    cc
    wcel
    #
    @63
    ax-1cn
    @33
    @4
    cn0
    wcel
    @64
    hashxplem.1
    @34
    @4
    nn0cn
    mp2b
    #
    @13
    c1
    @4
    adddir
    mp3an23
    syl
    @60
    @4
    @14
    caddc
    @4
    @65
    mulid2i
    oveq2i
    syl6eq
    adantr
    eqtrd
    adantr
    3eqtr4d
    ex
    findcard2s
end
