include "cioo.mm"
include "crn.mm"
include "cle.mm"
include "cxr.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cop.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "cif.mm"
include "wcel.mm"
include "co.mm"
include "wrex.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "wa.mm"
include "wbr.mm"
include "0le0.mm"
include "df-br.mm"
include "mpbi.mm"
include "0xr.mm"
include "opelxpi.mm"
include "mp2an.mm"
include "elin.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "wn.mm"
include "simplr.mm"
include "infeq1d.mm"
include "wne.mm"
include "simplll.mm"
include "simpllr.mm"
include "simpr.mm"
include "neqned.mm"
include "eqnetrrd.mm"
include "df-ioo.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxlb.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "supeq1d.mm"
include "ixxub.mm"
include "opeq12d.mm"
include "ioon0.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "wi.mm"
include "mpd.mm"
include "sylib.mm"
include "elind.mm"
include "eqeltrd.mm"
include "ifclda.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "fmpti.mm"

theorem ioorf
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ioorf.1: |- F = ( x e. ran (,) |-> if ( x = (/) , <. 0 , 0 >. , <. inf ( x , RR* , < ) , sup ( x , RR* , < ) >. ) )


  assert |- F : ran (,) --> ( <_ i^i ( RR* X. RR* ) )

  proof
    vx
    cioo
    crn
    #
    cle
    cxr
    cxr
    cxp
    #
    cin
    #
    vx
    cv
    #
    c0
    wceq
    #
    cc0
    cc0
    cop
    #
    @3
    cxr
    clt
    cinf
    #
    @3
    cxr
    clt
    csup
    #
    cop
    #
    cif
    #
    cF
    ioorf.1
    @3
    @0
    wcel
    #
    @3
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wceq
    #
    vb
    cxr
    wrex
    va
    cxr
    wrex
    #
    @9
    @2
    wcel
    #
    @1
    cr
    cpw
    #
    cioo
    wf
    cioo
    @1
    wfn
    @10
    @15
    wb
    ioof
    @1
    @17
    cioo
    ffn
    va
    vb
    cxr
    cxr
    @3
    cioo
    ovelrn
    mp2b
    @14
    @16
    va
    vb
    cxr
    cxr
    @11
    cxr
    wcel
    #
    @12
    cxr
    wcel
    #
    wa
    #
    @14
    @16
    @20
    @14
    wa
    #
    @4
    @5
    @8
    @2
    @5
    @2
    wcel
    #
    @21
    @4
    wa
    @22
    @5
    cle
    wcel
    #
    @5
    @1
    wcel
    #
    cc0
    cc0
    cle
    wbr
    @23
    0le0
    cc0
    cc0
    cle
    df-br
    mpbi
    cc0
    cxr
    wcel
    #
    @25
    @24
    0xr
    0xr
    cc0
    cc0
    cxr
    cxr
    opelxpi
    mp2an
    @5
    cle
    @1
    elin
    mpbir2an
    a1i
    @21
    @4
    wn
    #
    wa
    #
    @8
    @11
    @12
    cop
    #
    @2
    @27
    @6
    @11
    @7
    @12
    @27
    @6
    @13
    cxr
    clt
    cinf
    #
    @11
    @27
    cxr
    @3
    @13
    clt
    @20
    @14
    @26
    simplr
    #
    infeq1d
    @27
    @18
    @19
    @13
    c0
    wne
    #
    @29
    @11
    wceq
    @18
    @19
    @14
    @26
    simplll
    #
    @18
    @19
    @14
    @26
    simpllr
    #
    @27
    @3
    @13
    c0
    @30
    @27
    @3
    c0
    @21
    @26
    simpr
    neqned
    eqnetrrd
    #
    vx
    vy
    vz
    vw
    @11
    @12
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    #
    vw
    cv
    #
    cxr
    wcel
    #
    @19
    wa
    @36
    @12
    clt
    wbr
    idd
    #
    @36
    @12
    xrltle
    #
    @18
    @37
    wa
    @11
    @36
    clt
    wbr
    idd
    #
    @11
    @36
    xrltle
    #
    ixxlb
    syl3anc
    eqtrd
    @27
    @7
    @13
    cxr
    clt
    csup
    #
    @12
    @27
    cxr
    @3
    @13
    clt
    @30
    supeq1d
    @27
    @18
    @19
    @31
    @42
    @12
    wceq
    @32
    @33
    @34
    vx
    vy
    vz
    vw
    @11
    @12
    clt
    clt
    cioo
    @35
    @38
    @39
    @40
    @41
    ixxub
    syl3anc
    eqtrd
    opeq12d
    @27
    cle
    @1
    @28
    @27
    @11
    @12
    cle
    wbr
    #
    @28
    cle
    wcel
    @27
    @11
    @12
    clt
    wbr
    #
    @43
    @27
    @31
    @44
    @34
    @20
    @31
    @44
    wb
    @14
    @26
    @11
    @12
    ioon0
    ad2antrr
    mpbid
    @20
    @44
    @43
    wi
    @14
    @26
    @11
    @12
    xrltle
    ad2antrr
    mpd
    @11
    @12
    cle
    df-br
    sylib
    @20
    @28
    @1
    wcel
    @14
    @26
    @11
    @12
    cxr
    cxr
    opelxpi
    ad2antrr
    elind
    eqeltrd
    ifclda
    ex
    rexlimivv
    sylbi
    fmpti
end
