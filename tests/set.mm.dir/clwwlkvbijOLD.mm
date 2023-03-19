include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "clsw.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cclwwlkn.mm"
include "wf1o.mm"
include "wex.mm"
include "cop.mm"
include "csubstr.mm"
include "cmpt.mm"
include "cres.mm"
include "cvv.mm"
include "ovex.mm"
include "mptrabex.mm"
include "resex.mm"
include "eqid.mm"
include "clwwlkf1o.mm"
include "w3a.mm"
include "wb.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "3ad2ant3.mm"
include "cvtx.mm"
include "cword.mm"
include "c1.mm"
include "chash.mm"
include "cfz.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cfzo.mm"
include "wral.mm"
include "wwlknp.mm"
include "simpll.mm"
include "cuz.mm"
include "cz.mm"
include "nnz.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "elfz1end.mm"
include "biimpi.mm"
include "fzss2.mm"
include "sselda.mm"
include "syl2anc.mm"
include "adantl.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "3adant3.mm"
include "syl.mm"
include "sylbi.mm"
include "impcom.mm"
include "swrd0fv0.mm"
include "bitrd.mm"
include "f1oresrab.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "cbvrabv.mm"
include "f1oeq3.mm"
include "mp1i.mm"
include "exbidv.mm"
include "cab.mm"
include "df-rab.mm"
include "anass.mm"
include "bicomi.mm"
include "abbii.mm"
include "anbi1i.mm"
include "eqtr4i.mm"
include "3eqtri.mm"
include "f1oeq2.mm"

theorem clwwlkvbijOLD
  let vw: setvar w
  let cS: class S
  let vf: setvar f
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i

  disjoint G f
  disjoint G w
  disjoint f w
  disjoint N f
  disjoint N w
  disjoint S f
  disjoint S w
  disjoint G x
  disjoint G y
  disjoint f x
  disjoint f y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint G i
  disjoint i w
  disjoint N x
  disjoint N y
  disjoint N i
  disjoint S y
  assert |- ( N e. NN -> E. f f : { w e. ( N WWalksN G ) | ( ( lastS ` w ) = ( w ` 0 ) /\ ( w ` 0 ) = S ) } -1-1-onto-> { w e. ( N ClWWalksN G ) | ( w ` 0 ) = S } )

  proof
    cN
    cn
    wcel
    #
    vw
    cv
    #
    clsw
    cfv
    #
    cc0
    @1
    cfv
    #
    wceq
    #
    @3
    cS
    wceq
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    @5
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @5
    vw
    vx
    cv
    #
    clsw
    cfv
    #
    cc0
    @13
    cfv
    #
    wceq
    #
    vx
    @7
    crab
    #
    crab
    #
    @10
    @11
    wf1o
    #
    vf
    wex
    #
    @0
    @20
    @18
    cc0
    vy
    cv
    #
    cfv
    #
    cS
    wceq
    #
    vy
    @9
    crab
    #
    @11
    wf1o
    #
    vf
    wex
    #
    vw
    @17
    @1
    cc0
    cN
    cop
    csubstr
    co
    #
    cmpt
    #
    @18
    cres
    #
    cvv
    wcel
    @0
    @18
    @24
    @29
    wf1o
    #
    @26
    @28
    @18
    @16
    vw
    vx
    @7
    @27
    cN
    cG
    cwwlksn
    ovex
    mptrabex
    resex
    @0
    @5
    @23
    vw
    vy
    @17
    @9
    @27
    @28
    @28
    eqid
    #
    vx
    vw
    @17
    @28
    cG
    cN
    @17
    eqid
    @31
    clwwlkf1o
    @0
    @1
    @17
    wcel
    #
    @21
    @27
    wceq
    #
    w3a
    @23
    cc0
    @27
    cfv
    #
    cS
    wceq
    #
    @5
    @33
    @0
    @23
    @35
    wb
    @32
    @33
    @22
    @34
    cS
    cc0
    @21
    @27
    fveq1
    eqeq1d
    3ad2ant3
    @0
    @32
    @35
    @5
    wb
    @33
    @0
    @32
    wa
    #
    @34
    @3
    cS
    @36
    @1
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cN
    c1
    @1
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @34
    @3
    wceq
    @32
    @0
    @42
    @32
    @1
    @7
    wcel
    #
    @4
    wa
    #
    @0
    @42
    wi
    #
    @16
    @4
    vx
    @1
    @7
    @13
    @1
    wceq
    @14
    @2
    @15
    @3
    @13
    @1
    clsw
    fveq2
    cc0
    @13
    @1
    fveq1
    eqeq12d
    elrab
    #
    @43
    @45
    @4
    @43
    @38
    @39
    cN
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    @1
    cfv
    @49
    c1
    caddc
    co
    @1
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    @45
    vi
    @50
    cG
    cN
    @37
    @1
    @37
    eqid
    @50
    eqid
    wwlknp
    @38
    @48
    @45
    @51
    @38
    @48
    wa
    #
    @0
    @42
    @52
    @0
    wa
    #
    @38
    @41
    @38
    @48
    @0
    simpll
    @53
    @41
    cN
    c1
    @47
    cfz
    co
    #
    wcel
    #
    @0
    @55
    @52
    @0
    @47
    cN
    cuz
    cfv
    #
    wcel
    #
    cN
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @55
    @0
    cN
    cz
    wcel
    cN
    @56
    wcel
    @57
    cN
    nnz
    cN
    uzid
    cN
    cN
    peano2uz
    3syl
    @0
    @59
    cN
    elfz1end
    biimpi
    @57
    @58
    @54
    cN
    cN
    c1
    @47
    fzss2
    sselda
    syl2anc
    adantl
    @52
    @41
    @55
    wb
    #
    @0
    @48
    @60
    @38
    @48
    @40
    @54
    cN
    @39
    @47
    c1
    cfz
    oveq2
    eleq2d
    adantl
    adantr
    mpbird
    jca
    ex
    3adant3
    syl
    adantr
    sylbi
    impcom
    cN
    @37
    @1
    swrd0fv0
    syl
    eqeq1d
    3adant3
    bitrd
    f1oresrab
    @25
    @30
    vf
    @29
    cvv
    @18
    @24
    @11
    @29
    f1oeq1
    spcegv
    mpsyl
    @0
    @19
    @25
    vf
    @10
    @24
    wceq
    @19
    @25
    wb
    @0
    @5
    @23
    vw
    vy
    @9
    @1
    @21
    wceq
    @3
    @22
    cS
    cc0
    @1
    @21
    fveq1
    eqeq1d
    cbvrabv
    @10
    @24
    @18
    @11
    f1oeq3
    mp1i
    exbidv
    mpbird
    @0
    @12
    @19
    vf
    @8
    @18
    wceq
    @12
    @19
    wb
    @0
    @8
    @43
    @6
    wa
    #
    vw
    cab
    @44
    @5
    wa
    #
    vw
    cab
    #
    @18
    @6
    vw
    @7
    df-rab
    @61
    @62
    vw
    @62
    @61
    @43
    @4
    @5
    anass
    bicomi
    abbii
    @63
    @32
    @5
    wa
    #
    vw
    cab
    @18
    @62
    @64
    vw
    @44
    @32
    @5
    @32
    @44
    @46
    bicomi
    anbi1i
    abbii
    @5
    vw
    @17
    df-rab
    eqtr4i
    3eqtri
    @8
    @18
    @10
    @11
    f1oeq2
    mp1i
    exbidv
    mpbird
end
