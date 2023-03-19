include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "clsw.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cclwwlknon.mm"
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
include "cclwwlkn.mm"
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
include "clwwlknon.mm"
include "a1i.mm"
include "f1oeq3d.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "cab.mm"
include "df-rab.mm"
include "anass.mm"
include "bicomi.mm"
include "abbii.mm"
include "anbi1i.mm"
include "eqtr4i.mm"
include "3eqtri.mm"
include "f1oeq2.mm"
include "mp1i.mm"
include "exbidv.mm"

theorem clwwlkvbij
  let vw: setvar w
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  assume clwwlkvbij.v: |- V = ( Vtx ` G )

  disjoint G f
  disjoint G w
  disjoint f w
  disjoint N f
  disjoint N w
  disjoint V f
  disjoint X f
  disjoint X w
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
  disjoint X y
  assert |- ( ( X e. V /\ N e. NN ) -> E. f f : { w e. ( N WWalksN G ) | ( ( lastS ` w ) = ( w ` 0 ) /\ ( w ` 0 ) = X ) } -1-1-onto-> ( X ( ClWWalksNOn ` G ) N ) )

  proof
    cX
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    vw
    cv
    #
    clsw
    cfv
    #
    cc0
    @3
    cfv
    #
    wceq
    #
    @5
    cX
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
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    #
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @7
    vw
    vx
    cv
    #
    clsw
    cfv
    #
    cc0
    @14
    cfv
    #
    wceq
    #
    vx
    @9
    crab
    #
    crab
    #
    @11
    @12
    wf1o
    #
    vf
    wex
    #
    vw
    @18
    @3
    cc0
    cN
    cop
    csubstr
    co
    #
    cmpt
    #
    @19
    cres
    #
    cvv
    wcel
    @2
    @19
    @11
    @24
    wf1o
    #
    @21
    @23
    @19
    @17
    vw
    vx
    @9
    @22
    cN
    cG
    cwwlksn
    ovex
    mptrabex
    resex
    @2
    @25
    @19
    cc0
    vy
    cv
    #
    cfv
    #
    cX
    wceq
    #
    vy
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    @24
    wf1o
    #
    @1
    @31
    @0
    @1
    @7
    @28
    vw
    vy
    @18
    @29
    @22
    @23
    @23
    eqid
    #
    vx
    vw
    @18
    @23
    cG
    cN
    @18
    eqid
    @32
    clwwlkf1o
    @1
    @3
    @18
    wcel
    #
    @26
    @22
    wceq
    #
    w3a
    @28
    cc0
    @22
    cfv
    #
    cX
    wceq
    #
    @7
    @34
    @1
    @28
    @36
    wb
    @33
    @34
    @27
    @35
    cX
    cc0
    @26
    @22
    fveq1
    eqeq1d
    3ad2ant3
    @1
    @33
    @36
    @7
    wb
    @34
    @1
    @33
    wa
    #
    @35
    @5
    cX
    @37
    @3
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cN
    c1
    @3
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
    @35
    @5
    wceq
    @33
    @1
    @43
    @33
    @3
    @9
    wcel
    #
    @6
    wa
    #
    @1
    @43
    wi
    #
    @17
    @6
    vx
    @3
    @9
    @14
    @3
    wceq
    @15
    @4
    @16
    @5
    @14
    @3
    clsw
    fveq2
    cc0
    @14
    @3
    fveq1
    eqeq12d
    elrab
    #
    @44
    @46
    @6
    @44
    @39
    @40
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
    @3
    cfv
    @50
    c1
    caddc
    co
    @3
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
    @46
    vi
    @51
    cG
    cN
    @38
    @3
    @38
    eqid
    @51
    eqid
    wwlknp
    @39
    @49
    @46
    @52
    @39
    @49
    wa
    #
    @1
    @43
    @53
    @1
    wa
    #
    @39
    @42
    @39
    @49
    @1
    simpll
    @54
    @42
    cN
    c1
    @48
    cfz
    co
    #
    wcel
    #
    @1
    @56
    @53
    @1
    @48
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
    @56
    @1
    cN
    cz
    wcel
    cN
    @57
    wcel
    @58
    cN
    nnz
    cN
    uzid
    cN
    cN
    peano2uz
    3syl
    @1
    @60
    cN
    elfz1end
    biimpi
    @58
    @59
    @55
    cN
    cN
    c1
    @48
    fzss2
    sselda
    syl2anc
    adantl
    @53
    @42
    @56
    wb
    #
    @1
    @49
    @61
    @39
    @49
    @41
    @55
    cN
    @40
    @48
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
    @38
    @3
    swrd0fv0
    syl
    eqeq1d
    3adant3
    bitrd
    f1oresrab
    adantl
    @2
    @11
    @30
    @19
    @24
    @11
    @30
    wceq
    @2
    vy
    cG
    cN
    cX
    clwwlknon
    a1i
    f1oeq3d
    mpbird
    @20
    @25
    vf
    @24
    cvv
    @19
    @11
    @12
    @24
    f1oeq1
    spcegv
    mpsyl
    @2
    @13
    @20
    vf
    @10
    @19
    wceq
    @13
    @20
    wb
    @2
    @10
    @44
    @8
    wa
    #
    vw
    cab
    @45
    @7
    wa
    #
    vw
    cab
    #
    @19
    @8
    vw
    @9
    df-rab
    @62
    @63
    vw
    @63
    @62
    @44
    @6
    @7
    anass
    bicomi
    abbii
    @64
    @33
    @7
    wa
    #
    vw
    cab
    @19
    @63
    @65
    vw
    @45
    @33
    @7
    @33
    @45
    @47
    bicomi
    anbi1i
    abbii
    @7
    vw
    @18
    df-rab
    eqtr4i
    3eqtri
    @10
    @19
    @11
    @12
    f1oeq2
    mp1i
    exbidv
    mpbird
end
