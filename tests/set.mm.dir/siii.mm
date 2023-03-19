include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cn0v.mm"
include "wceq.mm"
include "cc0.mm"
include "oveq2.mm"
include "cnv.mm"
include "wcel.mm"
include "phnvi.mm"
include "eqid.mm"
include "dip0r.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "abs00bd.mm"
include "nvge0.mm"
include "nvcli.mm"
include "mulge0i.mm"
include "syl6eqbr.mm"
include "wne.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "csqrt.mm"
include "ccj.mm"
include "recni.mm"
include "sqeq0i.mm"
include "wb.mm"
include "nvz.mm"
include "bitri.mm"
include "necon3bii.mm"
include "cc.mm"
include "dipcl.mm"
include "mp3an.mm"
include "resqcli.mm"
include "divcan1zi.mm"
include "sylbir.mm"
include "dipcj.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "absval.mm"
include "ax-mp.mm"
include "syl6reqr.mm"
include "eqcomd.mm"
include "cr.mm"
include "wi.mm"
include "divclzi.mm"
include "ipipcj.mm"
include "mulcomli.mm"
include "oveq1i.mm"
include "wa.mm"
include "div23.mm"
include "mp3an12.mm"
include "mpan.mm"
include "syl5reqr.mm"
include "abscli.mm"
include "redivclzi.mm"
include "eqeltrd.mm"
include "clt.mm"
include "sqgt0i.mm"
include "sqge0i.mm"
include "divge0.mm"
include "mpanl12.mm"
include "sylancr.mm"
include "breqtrrd.mm"
include "cns.mm"
include "cnsb.mm"
include "siilem2.mm"
include "syl3anc.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "pm2.61ine.mm"

theorem siii
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cN: class N
  let cX: class X
  assume siii.1: |- X = ( BaseSet ` U )
  assume siii.6: |- N = ( normCV ` U )
  assume siii.7: |- P = ( .iOLD ` U )
  assume siii.9: |- U e. CPreHilOLD
  assume siii.a: |- A e. X
  assume siii.b: |- B e. X


  assert |- ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) )

  proof
    cA
    cB
    cP
    co
    #
    cabs
    cfv
    #
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    cB
    cU
    cn0v
    cfv
    #
    cB
    @5
    wceq
    #
    @1
    cc0
    @4
    cle
    @6
    @0
    @6
    @0
    cA
    @5
    cP
    co
    #
    cc0
    cB
    @5
    cA
    cP
    oveq2
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    @7
    cc0
    wceq
    cU
    siii.9
    phnvi
    #
    siii.a
    cA
    cP
    cU
    cX
    @5
    siii.1
    @5
    eqid
    #
    siii.7
    dip0r
    mp2an
    syl6eq
    abs00bd
    cc0
    @2
    cle
    wbr
    #
    cc0
    @3
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    @8
    @9
    @12
    @10
    siii.a
    cA
    cU
    cN
    cX
    siii.1
    siii.6
    nvge0
    mp2an
    @8
    cB
    cX
    wcel
    #
    @13
    @10
    siii.b
    cB
    cU
    cN
    cX
    siii.1
    siii.6
    nvge0
    mp2an
    @2
    @3
    cA
    cU
    cN
    cX
    siii.1
    siii.6
    @10
    siii.a
    nvcli
    cB
    cU
    cN
    cX
    siii.1
    siii.6
    @10
    siii.b
    nvcli
    #
    mulge0i
    mp2an
    syl6eqbr
    cB
    @5
    wne
    #
    @1
    @0
    cB
    cA
    cP
    co
    #
    @3
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @18
    cmul
    co
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    @4
    cle
    @16
    @22
    @0
    @0
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    @1
    @16
    @21
    @24
    csqrt
    @16
    @20
    @23
    @0
    cmul
    @16
    @20
    @17
    @23
    @16
    @18
    cc0
    wne
    #
    @20
    @17
    wceq
    @18
    cc0
    cB
    @5
    @18
    cc0
    wceq
    @3
    cc0
    wceq
    #
    @6
    @3
    @3
    @15
    recni
    sqeq0i
    @8
    @14
    @27
    @6
    wb
    @10
    siii.b
    cB
    cU
    cN
    cX
    @5
    siii.1
    @11
    siii.6
    nvz
    mp2an
    #
    bitri
    necon3bii
    #
    @17
    @18
    @8
    @14
    @9
    @17
    cc
    wcel
    #
    @10
    siii.b
    siii.a
    cB
    cA
    cP
    cU
    cX
    siii.1
    siii.7
    dipcl
    mp3an
    #
    @18
    @3
    @15
    resqcli
    #
    recni
    #
    divcan1zi
    sylbir
    #
    @8
    @9
    @14
    @23
    @17
    wceq
    @10
    siii.a
    siii.b
    cA
    cB
    cP
    cU
    cX
    siii.1
    siii.7
    dipcj
    mp3an
    syl6eqr
    oveq2d
    fveq2d
    @0
    cc
    wcel
    #
    @1
    @25
    wceq
    @8
    @9
    @14
    @35
    @10
    siii.a
    siii.b
    cA
    cB
    cP
    cU
    cX
    siii.1
    siii.7
    dipcl
    mp3an
    #
    @0
    absval
    ax-mp
    syl6reqr
    @16
    @17
    @20
    wceq
    #
    @22
    @4
    cle
    wbr
    #
    @16
    @20
    @17
    @34
    eqcomd
    @16
    @19
    cc
    wcel
    #
    @19
    @0
    cmul
    co
    #
    cr
    wcel
    cc0
    @40
    cle
    wbr
    @37
    @38
    wi
    @16
    @26
    @39
    @29
    @17
    @18
    @31
    @33
    divclzi
    sylbir
    @16
    @40
    @1
    c2
    cexp
    co
    #
    @18
    cdiv
    co
    #
    cr
    @16
    @42
    @17
    @0
    cmul
    co
    #
    @18
    cdiv
    co
    #
    @40
    @43
    @41
    @18
    cdiv
    @0
    @17
    @41
    @36
    @31
    @8
    @9
    @14
    @0
    @17
    cmul
    co
    @41
    wceq
    @10
    siii.a
    siii.b
    cA
    cB
    cP
    cU
    cX
    siii.1
    siii.7
    ipipcj
    mp3an
    mulcomli
    oveq1i
    @16
    @26
    @44
    @40
    wceq
    #
    @29
    @18
    cc
    wcel
    #
    @26
    @45
    @33
    @30
    @35
    @46
    @26
    wa
    @45
    @31
    @36
    @17
    @0
    @18
    div23
    mp3an12
    mpan
    sylbir
    syl5reqr
    #
    @16
    @26
    @42
    cr
    wcel
    @29
    @41
    @18
    @1
    @0
    @36
    abscli
    #
    resqcli
    #
    @32
    redivclzi
    sylbir
    eqeltrd
    @16
    cc0
    @42
    @40
    cle
    @16
    @18
    cr
    wcel
    #
    cc0
    @18
    clt
    wbr
    #
    cc0
    @42
    cle
    wbr
    #
    @32
    @16
    @3
    cc0
    wne
    @51
    @3
    cc0
    cB
    @5
    @28
    necon3bii
    @3
    @15
    sqgt0i
    sylbir
    @41
    cr
    wcel
    cc0
    @41
    cle
    wbr
    @50
    @51
    wa
    @52
    @49
    @1
    @48
    sqge0i
    @41
    @18
    divge0
    mpanl12
    sylancr
    @47
    breqtrrd
    cA
    cB
    @19
    cP
    cU
    cns
    cfv
    #
    cU
    cU
    cnsb
    cfv
    #
    cN
    cX
    siii.1
    siii.6
    siii.7
    siii.9
    siii.a
    siii.b
    @54
    eqid
    @53
    eqid
    siilem2
    syl3anc
    mpd
    eqbrtrd
    pm2.61ine
end
