include "cc0.mm"
include "cpi.mm"
include "cicc.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "ccos.mm"
include "cres.mm"
include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cosf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "cr.mm"
include "0re.mm"
include "pire.mm"
include "iccssre.mm"
include "mp2an.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "fnssres.mm"
include "fvres.mm"
include "sseli.mm"
include "cosbnd2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wa.mm"
include "eqeqan12d.mm"
include "cos11.mm"
include "biimprd.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "wrex.mm"
include "a1i.mm"
include "cle.mm"
include "wbr.mm"
include "neg1rr.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "clt.mm"
include "pipos.mm"
include "ccncf.mm"
include "coscn.mm"
include "recoscld.mm"
include "adantl.mm"
include "cospi.mm"
include "simp2bi.mm"
include "syl5eqbr.mm"
include "simp3bi.mm"
include "cos0.mm"
include "syl6breqr.mm"
include "jca.mm"
include "ivthle2.mm"
include "eqcom.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "rexbiia.mm"
include "sylibr.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem recosf1o
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( cos |` ( 0 [,] _pi ) ) : ( 0 [,] _pi ) -1-1-onto-> ( -u 1 [,] 1 )

  proof
    cc0
    cpi
    cicc
    co
    #
    c1
    cneg
    #
    c1
    cicc
    co
    #
    ccos
    @0
    cres
    #
    wf1o
    @0
    @2
    @3
    wf1
    #
    @0
    @2
    @3
    wfo
    #
    @4
    @0
    @2
    @3
    wf
    #
    vx
    cv
    #
    @3
    cfv
    #
    vy
    cv
    #
    @3
    cfv
    #
    wceq
    #
    @7
    @9
    wceq
    #
    wi
    #
    vy
    @0
    wral
    vx
    @0
    wral
    @6
    @3
    @0
    wfn
    #
    @8
    @2
    wcel
    #
    vx
    @0
    wral
    ccos
    cc
    wfn
    #
    @0
    cc
    wss
    #
    @14
    cc
    cc
    ccos
    wf
    @16
    cosf
    cc
    cc
    ccos
    ffn
    ax-mp
    @0
    cr
    cc
    cc0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @0
    cr
    wss
    0re
    pire
    cc0
    cpi
    iccssre
    mp2an
    #
    ax-resscn
    sstri
    #
    cc
    @0
    ccos
    fnssres
    mp2an
    @15
    vx
    @0
    @7
    @0
    wcel
    #
    @8
    @7
    ccos
    cfv
    #
    @2
    @7
    @0
    ccos
    fvres
    #
    @22
    @7
    cr
    wcel
    #
    @23
    @2
    wcel
    @0
    cr
    @7
    @20
    sseli
    @7
    cosbnd2
    syl
    eqeltrd
    rgen
    vx
    @0
    @2
    @3
    ffnfv
    mpbir2an
    #
    @13
    vx
    vy
    @0
    @22
    @9
    @0
    wcel
    #
    wa
    #
    @11
    @23
    @9
    ccos
    cfv
    #
    wceq
    #
    @12
    @22
    @27
    @8
    @23
    @10
    @29
    @24
    @9
    @0
    ccos
    fvres
    #
    eqeqan12d
    @28
    @12
    @30
    @7
    @9
    cos11
    biimprd
    sylbid
    rgen2a
    vx
    vy
    @0
    @2
    @3
    dff13
    mpbir2an
    @5
    @6
    @7
    @10
    wceq
    #
    vy
    @0
    wrex
    #
    vx
    @2
    wral
    @26
    @33
    vx
    @2
    @7
    @2
    wcel
    #
    @29
    @7
    wceq
    #
    vy
    @0
    wrex
    @33
    @34
    vz
    cc0
    cpi
    cc
    @7
    ccos
    vy
    @18
    @34
    0re
    a1i
    @19
    @34
    pire
    a1i
    @34
    @25
    @1
    @7
    cle
    wbr
    #
    @7
    c1
    cle
    wbr
    #
    @1
    c1
    @7
    neg1rr
    1re
    elicc2i
    #
    simp1bi
    cc0
    cpi
    clt
    wbr
    @34
    pipos
    a1i
    @17
    @34
    @21
    a1i
    ccos
    cc
    cc
    ccncf
    co
    wcel
    @34
    coscn
    a1i
    vz
    cv
    #
    @0
    wcel
    #
    @39
    ccos
    cfv
    cr
    wcel
    @34
    @40
    @39
    @0
    cr
    @39
    @20
    sseli
    recoscld
    adantl
    @34
    cpi
    ccos
    cfv
    #
    @7
    cle
    wbr
    @7
    cc0
    ccos
    cfv
    #
    cle
    wbr
    @34
    @41
    @1
    @7
    cle
    cospi
    @34
    @25
    @36
    @37
    @38
    simp2bi
    syl5eqbr
    @34
    @7
    c1
    @42
    cle
    @34
    @25
    @36
    @37
    @38
    simp3bi
    cos0
    syl6breqr
    jca
    ivthle2
    @32
    @35
    vy
    @0
    @32
    @10
    @7
    wceq
    @27
    @35
    @7
    @10
    eqcom
    @27
    @10
    @29
    @7
    @31
    eqeq1d
    syl5bb
    rexbiia
    sylibr
    rgen
    vy
    vx
    @0
    @2
    @3
    dffo3
    mpbir2an
    @0
    @2
    @3
    df-f1o
    mpbir2an
end
