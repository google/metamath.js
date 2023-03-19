include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cvol.mm"
include "csumge0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "cle.mm"
include "cin.mm"
include "wcel.mm"
include "wf.mm"
include "c1st.mm"
include "c2nd.mm"
include "wbr.mm"
include "cif.mm"
include "cop.mm"
include "iftrue.mm"
include "opeq2d.mm"
include "adantl.mm"
include "df-br.mm"
include "biimpi.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "leidd.mm"
include "sylib.mm"
include "adantr.mm"
include "pm2.61dan.mm"
include "xp2nd.mm"
include "ifcld.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "elind.mm"
include "fmptd.mm"
include "cvv.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "a1i.mm"
include "nnex.mm"
include "elmapd.mm"
include "mpbird.mm"
include "simpr.mm"
include "rexpssxrxp.mm"
include "fssd.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "cbvrabv.mm"
include "ovolval4lem1.mm"
include "simpld.mm"
include "sseqtrd.mm"
include "adantrr.mm"
include "simprd.mm"
include "coass.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "adantrl.mm"
include "jca.mm"
include "coeq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "rexlimiva.mm"
include "inss2.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "impbii.mm"
include "rabbii.mm"
include "eqtri.mm"
include "ovolval3.mm"

theorem ovolval4lem2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let cM: class M
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  assume ovolval4lem2.a: |- ( ph -> A C_ RR )
  assume ovolval4lem2.m: |- M = { y e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = ( sum^ ` ( ( vol o. (,) ) o. f ) ) ) }
  assume ovolval4lem2.g: |- G = ( n e. NN |-> <. ( 1st ` ( f ` n ) ) , if ( ( 1st ` ( f ` n ) ) <_ ( 2nd ` ( f ` n ) ) , ( 2nd ` ( f ` n ) ) , ( 1st ` ( f ` n ) ) ) >. )

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint G n
  disjoint f n
  disjoint ph y
  disjoint A g
  disjoint f g
  disjoint g y
  disjoint G g
  disjoint f k
  disjoint k n
  disjoint g ph
  disjoint k x
  assert |- ( ph -> ( vol* ` A ) = inf ( M , RR* , < ) )

  proof
    wph
    vy
    cA
    vg
    cM
    ovolval4lem2.a
    cM
    cA
    cioo
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    vy
    cv
    #
    cvol
    cioo
    ccom
    #
    @0
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    cr
    cr
    cxp
    #
    cn
    cmap
    co
    #
    wrex
    #
    vy
    cxr
    crab
    cA
    cioo
    vg
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    @5
    @6
    @14
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vg
    cle
    @11
    cin
    #
    cn
    cmap
    co
    #
    wrex
    #
    vy
    cxr
    crab
    ovolval4lem2.m
    @13
    @25
    vy
    cxr
    @13
    @25
    @10
    @25
    vf
    @12
    @0
    @12
    wcel
    #
    @10
    wa
    #
    cG
    @24
    wcel
    #
    cA
    cioo
    cG
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    @5
    @6
    cG
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    @25
    @26
    @28
    @10
    @26
    @28
    cn
    @23
    cG
    wf
    @26
    vn
    cn
    vn
    cv
    #
    @0
    cfv
    #
    c1st
    cfv
    #
    @39
    @38
    c2nd
    cfv
    #
    cle
    wbr
    #
    @40
    @39
    cif
    #
    cop
    #
    @23
    cG
    @26
    @37
    cn
    wcel
    wa
    #
    cle
    @11
    @43
    @44
    @41
    @43
    cle
    wcel
    @44
    @41
    wa
    @43
    @39
    @40
    cop
    #
    cle
    @41
    @43
    @45
    wceq
    @44
    @41
    @42
    @40
    @39
    @41
    @40
    @39
    iftrue
    opeq2d
    adantl
    @41
    @45
    cle
    wcel
    #
    @44
    @41
    @46
    @39
    @40
    cle
    df-br
    biimpi
    adantl
    eqeltrd
    @44
    @41
    wn
    #
    wa
    @43
    @39
    @39
    cop
    #
    cle
    @47
    @43
    @48
    wceq
    @44
    @47
    @42
    @39
    @39
    @41
    @40
    @39
    iffalse
    opeq2d
    adantl
    @44
    @48
    cle
    wcel
    #
    @47
    @44
    @39
    @39
    cle
    wbr
    @49
    @44
    @39
    @44
    @38
    @11
    wcel
    #
    @39
    cr
    wcel
    #
    @26
    cn
    @11
    @37
    @0
    @0
    @11
    cn
    elmapi
    #
    ffvelrnda
    #
    @38
    cr
    cr
    xp1st
    syl
    #
    leidd
    @39
    @39
    cle
    df-br
    sylib
    adantr
    eqeltrd
    pm2.61dan
    @44
    @51
    @42
    cr
    wcel
    @43
    @11
    wcel
    @54
    @44
    @41
    @40
    @39
    cr
    @44
    @50
    @40
    cr
    wcel
    @53
    @38
    cr
    cr
    xp2nd
    syl
    @54
    ifcld
    @39
    @42
    cr
    cr
    opelxpi
    syl2anc
    elind
    ovolval4lem2.g
    fmptd
    @26
    @23
    cn
    cG
    cvv
    cvv
    @23
    cvv
    wcel
    @26
    @11
    cle
    cr
    cr
    reex
    reex
    xpex
    #
    inex2
    a1i
    cn
    cvv
    wcel
    @26
    nnex
    a1i
    elmapd
    mpbird
    adantr
    @27
    @32
    @35
    @26
    @4
    @32
    @9
    @26
    @4
    wa
    cA
    @3
    @31
    @26
    @4
    simpr
    @26
    @3
    @31
    wceq
    #
    @4
    @26
    @56
    cvol
    @1
    ccom
    #
    cvol
    @29
    ccom
    #
    wceq
    #
    @26
    vk
    cv
    #
    @0
    cfv
    #
    c1st
    cfv
    #
    @61
    c2nd
    cfv
    #
    cle
    wbr
    #
    vk
    cn
    crab
    vn
    @0
    cG
    @26
    cn
    @11
    cxr
    cxr
    cxp
    #
    @0
    @52
    @11
    @65
    wss
    @26
    rexpssxrxp
    a1i
    fssd
    ovolval4lem2.g
    @64
    @41
    vk
    vn
    cn
    @60
    @37
    wceq
    #
    @62
    @39
    @63
    @40
    cle
    @66
    @61
    @38
    c1st
    @60
    @37
    @0
    fveq2
    #
    fveq2d
    @66
    @61
    @38
    c2nd
    @67
    fveq2d
    breq12d
    cbvrabv
    ovolval4lem1
    #
    simpld
    adantr
    sseqtrd
    adantrr
    @26
    @9
    @35
    @4
    @26
    @9
    wa
    @5
    @8
    @34
    @26
    @9
    simpr
    @26
    @8
    @34
    wceq
    @9
    @26
    @7
    @33
    csumge0
    @26
    @57
    @58
    @7
    @33
    @26
    @56
    @59
    @68
    simprd
    @7
    @57
    wceq
    @26
    cvol
    cioo
    @0
    coass
    a1i
    @33
    @58
    wceq
    @26
    cvol
    cioo
    cG
    coass
    a1i
    3eqtr4d
    fveq2d
    adantr
    eqtrd
    adantrl
    jca
    @22
    @36
    vg
    cG
    @24
    @14
    cG
    wceq
    #
    @18
    @32
    @21
    @35
    @69
    @17
    @31
    cA
    @69
    @16
    @30
    @69
    @15
    @29
    @14
    cG
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    @69
    @20
    @34
    @5
    @69
    @19
    @33
    csumge0
    @14
    cG
    @6
    coeq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    rexlimiva
    @22
    @13
    vg
    @24
    @14
    @24
    wcel
    #
    @22
    wa
    @14
    @12
    wcel
    #
    @22
    @13
    @70
    @71
    @22
    @24
    @12
    @14
    @11
    cvv
    wcel
    @23
    @11
    wss
    @24
    @12
    wss
    @55
    cle
    @11
    inss2
    @23
    @11
    cn
    cvv
    mapss
    mp2an
    sseli
    adantr
    @70
    @22
    simpr
    @10
    @22
    vf
    @14
    @12
    @0
    @14
    wceq
    #
    @4
    @18
    @9
    @21
    @72
    @3
    @17
    cA
    @72
    @2
    @16
    @72
    @1
    @15
    @0
    @14
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    @72
    @8
    @20
    @5
    @72
    @7
    @19
    csumge0
    @0
    @14
    @6
    coeq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    rexlimiva
    impbii
    rabbii
    eqtri
    ovolval3
end
