include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wtru.mm"
include "pire.mm"
include "renegcli.mm"
include "a1i.mm"
include "clt.mm"
include "pirp.mm"
include "neglt.mm"
include "ax-mp.mm"
include "ltleii.mm"
include "ccncf.mm"
include "fourierdlem62.mm"
include "evthiccabs.mm"
include "trud.mm"
include "simpli.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "simpl.mm"
include "fourierdlem43.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "remulcld.mm"
include "recnd.mm"
include "abscld.mm"
include "absge0d.mm"
include "ge0p1rpd.mm"
include "3ad2antl2.mm"
include "3adant3.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simpl11.mm"
include "simpl12.mm"
include "jca.mm"
include "simpl13.mm"
include "rspa.mm"
include "sylancom.mm"
include "simpl2.mm"
include "jca31.mm"
include "3ad2antl3.mm"
include "simpr.mm"
include "simp-5l.mm"
include "wceq.mm"
include "fourierdlem9.mm"
include "ffvelrnda.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "simp-5r.mm"
include "simpllr.mm"
include "peano2re.mm"
include "syl.mm"
include "fveq2d.mm"
include "recn.mm"
include "cc0.mm"
include "ad4ant14.mm"
include "ad3antlr.mm"
include "simplr.mm"
include "leabsd.mm"
include "letrd.mm"
include "lemul12bd.mm"
include "absmuld.mm"
include "cc.mm"
include "adantr.mm"
include "3brtr4d.mm"
include "eqbrtrd.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ltled.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem fourierdlem77
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume fourierdlem77.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem77.x: |- ( ph -> X e. RR )
  assume fourierdlem77.y: |- ( ph -> Y e. RR )
  assume fourierdlem77.w: |- ( ph -> W e. RR )
  assume fourierdlem77.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem77.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem77.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem77.bd: |- ( ph -> E. a e. RR A. s e. ( -u _pi [,] _pi ) ( abs ` ( H ` s ) ) <_ a )

  disjoint K b
  disjoint K s
  disjoint b s
  disjoint U a
  disjoint U b
  disjoint a b
  disjoint a ph
  disjoint a s
  disjoint ph s
  disjoint H c
  disjoint K c
  disjoint b c
  disjoint c s
  disjoint K x
  disjoint K y
  disjoint x y
  disjoint U c
  disjoint a c
  disjoint c ph
  disjoint k x
  assert |- ( ph -> E. b e. RR+ A. s e. ( -u _pi [,] _pi ) ( abs ` ( U ` s ) ) <_ b )

  proof
    wph
    vs
    cv
    #
    cH
    cfv
    #
    cabs
    cfv
    #
    va
    cv
    #
    cle
    wbr
    #
    vs
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wral
    #
    va
    cr
    wrex
    @0
    cU
    cfv
    #
    cabs
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vs
    @6
    wral
    #
    vb
    crp
    wrex
    #
    fourierdlem77.bd
    wph
    @7
    @13
    va
    cr
    wph
    @3
    cr
    wcel
    #
    @7
    w3a
    #
    @0
    cK
    cfv
    #
    cabs
    cfv
    #
    vc
    cv
    #
    cK
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vs
    @6
    wral
    #
    vc
    @6
    wrex
    #
    @13
    @23
    @15
    @23
    vx
    cv
    cK
    cfv
    cabs
    cfv
    vy
    cv
    cK
    cfv
    cabs
    cfv
    cle
    wbr
    vy
    @6
    wral
    vx
    @6
    wrex
    #
    @23
    @24
    wa
    wtru
    vc
    vs
    vx
    vy
    @5
    cpi
    cK
    @5
    cr
    wcel
    wtru
    cpi
    pire
    renegcli
    #
    a1i
    cpi
    cr
    wcel
    wtru
    pire
    a1i
    @5
    cpi
    cle
    wbr
    wtru
    @5
    cpi
    @25
    pire
    cpi
    crp
    wcel
    @5
    cpi
    clt
    wbr
    pirp
    cpi
    neglt
    ax-mp
    ltleii
    a1i
    cK
    @6
    cr
    ccncf
    co
    wcel
    wtru
    vs
    cK
    fourierdlem77.k
    fourierdlem62
    a1i
    evthiccabs
    trud
    simpli
    a1i
    @15
    @22
    @13
    vc
    @6
    @15
    @18
    @6
    wcel
    #
    @22
    w3a
    #
    @3
    @19
    cmul
    co
    #
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    crp
    wcel
    #
    @9
    @30
    cle
    wbr
    #
    vs
    @6
    wral
    #
    @13
    @15
    @26
    @31
    @22
    @14
    wph
    @26
    @31
    @7
    @14
    @26
    wa
    #
    @29
    @34
    @28
    @34
    @28
    @34
    @3
    @19
    @14
    @26
    simpl
    @26
    @19
    cr
    wcel
    @14
    @6
    cr
    @18
    cK
    cK
    vs
    fourierdlem77.k
    fourierdlem43
    #
    ffvelrni
    #
    adantl
    #
    remulcld
    recnd
    #
    abscld
    #
    @34
    @28
    @38
    absge0d
    ge0p1rpd
    3ad2antl2
    3adant3
    @27
    @32
    vs
    @6
    @15
    @26
    @22
    vs
    wph
    @14
    @7
    vs
    wph
    vs
    nfv
    @14
    vs
    nfv
    @4
    vs
    @6
    nfra1
    nf3an
    @26
    vs
    nfv
    @21
    vs
    @6
    nfra1
    nf3an
    @27
    @0
    @6
    wcel
    #
    @32
    @27
    @40
    wa
    #
    wph
    @14
    wa
    #
    @4
    wa
    #
    @26
    wa
    #
    @21
    @40
    @32
    @41
    @42
    @4
    @26
    @41
    wph
    @14
    wph
    @14
    @7
    @26
    @22
    @40
    simpl11
    wph
    @14
    @7
    @26
    @22
    @40
    simpl12
    jca
    @27
    @40
    @7
    @4
    wph
    @14
    @7
    @26
    @22
    @40
    simpl13
    @4
    vs
    @6
    rspa
    sylancom
    @15
    @26
    @22
    @40
    simpl2
    jca31
    @22
    @15
    @40
    @21
    @26
    @21
    vs
    @6
    rspa
    3ad2antl3
    @27
    @40
    simpr
    @44
    @21
    wa
    #
    @40
    wa
    #
    @9
    @30
    @45
    @40
    wph
    @9
    cr
    wcel
    wph
    @14
    @4
    @26
    @21
    @40
    simp-5l
    #
    wph
    @40
    wa
    #
    @8
    @48
    @8
    @48
    @8
    @1
    @16
    cmul
    co
    #
    cr
    @48
    @40
    @49
    cr
    wcel
    @8
    @49
    wceq
    wph
    @40
    simpr
    @48
    @1
    @16
    wph
    @6
    cr
    @0
    cH
    wph
    cF
    cH
    cW
    cX
    cY
    vs
    fourierdlem77.f
    fourierdlem77.x
    fourierdlem77.y
    fourierdlem77.w
    fourierdlem77.h
    fourierdlem9
    ffvelrnda
    #
    @40
    @16
    cr
    wcel
    wph
    @6
    cr
    @0
    cK
    @35
    ffvelrni
    #
    adantl
    #
    remulcld
    #
    vs
    @6
    @49
    cr
    cU
    fourierdlem77.u
    fvmpt2
    syl2anc
    #
    @53
    eqeltrd
    recnd
    abscld
    sylancom
    #
    @46
    @29
    cr
    wcel
    #
    @30
    cr
    wcel
    @46
    @14
    @26
    @56
    wph
    @14
    @4
    @26
    @21
    @40
    simp-5r
    #
    @43
    @26
    @21
    @40
    simpllr
    #
    @39
    syl2anc
    #
    @29
    peano2re
    syl
    #
    @46
    @9
    @29
    @30
    @55
    @59
    @60
    @46
    @9
    @49
    cabs
    cfv
    #
    @29
    cle
    @45
    @40
    wph
    @9
    @61
    wceq
    @47
    @48
    @8
    @49
    cabs
    @54
    fveq2d
    sylancom
    @46
    @2
    @17
    cmul
    co
    #
    @3
    cabs
    cfv
    #
    @20
    cmul
    co
    #
    @61
    @29
    cle
    @46
    @2
    @63
    @17
    @20
    @45
    @40
    wph
    @2
    cr
    wcel
    #
    @47
    @48
    @1
    @48
    @1
    @50
    recnd
    #
    abscld
    #
    sylancom
    @46
    @14
    @63
    cr
    wcel
    #
    @57
    @14
    @3
    @3
    recn
    #
    abscld
    #
    syl
    @40
    @17
    cr
    wcel
    @45
    @40
    @16
    @40
    @16
    @51
    recnd
    abscld
    adantl
    @46
    @26
    @20
    cr
    wcel
    @58
    @26
    @19
    @26
    @19
    @36
    recnd
    #
    abscld
    syl
    @45
    @40
    wph
    cc0
    @2
    cle
    wbr
    @47
    @48
    @1
    @66
    absge0d
    sylancom
    @46
    @26
    cc0
    @20
    cle
    wbr
    @58
    @26
    @19
    @71
    absge0d
    syl
    @43
    @40
    @2
    @63
    cle
    wbr
    @26
    @21
    @43
    @40
    wa
    #
    @2
    @3
    @63
    wph
    @40
    @65
    @14
    @4
    @67
    ad4ant14
    wph
    @14
    @4
    @40
    simpllr
    #
    @14
    @68
    wph
    @4
    @40
    @70
    ad3antlr
    @42
    @4
    @40
    simplr
    @72
    @3
    @73
    leabsd
    letrd
    ad4ant14
    @44
    @21
    @40
    simplr
    lemul12bd
    @45
    @40
    wph
    @61
    @62
    wceq
    @47
    @48
    @1
    @16
    @66
    @48
    @16
    @52
    recnd
    absmuld
    sylancom
    @46
    @14
    @26
    @29
    @64
    wceq
    @57
    @58
    @34
    @3
    @19
    @14
    @3
    cc
    wcel
    @26
    @69
    adantr
    @34
    @19
    @37
    recnd
    absmuld
    syl2anc
    3brtr4d
    eqbrtrd
    @46
    @29
    @59
    ltp1d
    lelttrd
    ltled
    syl21anc
    ex
    ralrimi
    @12
    @33
    vb
    @30
    crp
    @10
    @30
    wceq
    @11
    @32
    vs
    @6
    @10
    @30
    @9
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    rexlimdv3a
    mpd
    rexlimdv3a
    mpd
end
