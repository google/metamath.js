include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "clt.mm"
include "c2.mm"
include "cv.mm"
include "cle.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cwlks.mm"
include "pthiswlk.mm"
include "wlkv.mm"
include "syl.mm"
include "ctrls.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "ispth.mm"
include "a1i.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "caddc.mm"
include "csn.mm"
include "wss.mm"
include "wif.mm"
include "wa.mm"
include "istrl.mm"
include "eqid.mm"
include "iswlkg.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "wn.mm"
include "wne.mm"
include "pthdadjvtx.mm"
include "ad5ant245.mm"
include "neneqd.mm"
include "ifpfal.mm"
include "adantl.mm"
include "fvexd.mm"
include "neqne.mm"
include "prsshashgt1.mm"
include "syl31anc.mm"
include "sylbid.mm"
include "mpdan.mm"
include "ralimdva.mm"
include "ex.mm"
include "com23.mm"
include "exp31.mm"
include "com24.mm"
include "3impia.mm"
include "exp4c.mm"
include "imp.mm"
include "com14.mm"
include "3imp.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "mpcom.mm"
include "pm2.43i.mm"

theorem 2pthnloop
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  assume 2pthnloop.i: |- I = ( iEdg ` G )

  disjoint F i
  disjoint G i
  disjoint I i
  disjoint P i
  assert |- ( ( F ( Paths ` G ) P /\ 1 < ( # ` F ) ) -> A. i e. ( 0 ..^ ( # ` F ) ) 2 <_ ( # ` ( I ` ( F ` i ) ) ) )

  proof
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    c1
    cF
    chash
    cfv
    #
    clt
    wbr
    #
    c2
    vi
    cv
    #
    cF
    cfv
    #
    cI
    cfv
    #
    chash
    cfv
    cle
    wbr
    #
    vi
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    @0
    @2
    @8
    wi
    #
    cG
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    #
    @0
    @0
    @9
    wi
    #
    @0
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @13
    cP
    cF
    cG
    pthiswlk
    cP
    cF
    cG
    wlkv
    syl
    @10
    @11
    @0
    @14
    wi
    @12
    @10
    @0
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    c1
    @1
    cfzo
    co
    #
    cres
    ccnv
    wfun
    #
    cP
    cc0
    @1
    cpr
    cima
    cP
    @17
    cima
    cin
    c0
    wceq
    #
    w3a
    #
    @14
    @0
    @20
    wb
    @10
    cP
    cF
    cG
    ispth
    a1i
    @20
    @10
    @14
    @16
    @18
    @19
    @10
    @14
    wi
    @10
    @18
    @19
    @16
    @14
    @10
    @16
    @19
    @18
    @14
    @10
    @16
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    @1
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @3
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @5
    @24
    csn
    wceq
    #
    @24
    @26
    cpr
    @5
    wss
    #
    wif
    #
    vi
    @7
    wral
    #
    w3a
    #
    cF
    ccnv
    wfun
    #
    wa
    #
    @19
    @18
    @14
    wi
    wi
    #
    @16
    @15
    @33
    wa
    @10
    @34
    cP
    cF
    cG
    istrl
    @10
    @15
    @32
    @33
    cP
    vi
    cF
    cG
    cI
    @22
    cvv
    @22
    eqid
    2pthnloop.i
    iswlkg
    anbi1d
    syl5bb
    @34
    @35
    wi
    @10
    @32
    @33
    @35
    @32
    @33
    @19
    @18
    @14
    @21
    @23
    @31
    @33
    @19
    wa
    @18
    wa
    #
    @14
    wi
    @21
    @23
    wa
    #
    @0
    @36
    @31
    @9
    @37
    @0
    @36
    @31
    @9
    wi
    @37
    @0
    wa
    @36
    wa
    #
    @2
    @31
    @8
    @38
    @2
    @31
    @8
    wi
    @38
    @2
    wa
    #
    @30
    @6
    vi
    @7
    @39
    @3
    @7
    wcel
    #
    wa
    #
    @27
    wn
    #
    @30
    @6
    wi
    @41
    @24
    @26
    @0
    @2
    @40
    @24
    @26
    wne
    #
    @37
    @36
    cP
    cF
    cG
    @3
    pthdadjvtx
    ad5ant245
    neneqd
    @41
    @42
    wa
    @30
    @29
    @6
    @42
    @30
    @29
    wb
    @41
    @27
    @28
    @29
    ifpfal
    adantl
    @42
    @29
    @6
    wi
    #
    @41
    @42
    @24
    cvv
    wcel
    @26
    cvv
    wcel
    @43
    @5
    cvv
    wcel
    @44
    @42
    @3
    cP
    fvexd
    @42
    @25
    cP
    fvexd
    @24
    @26
    neqne
    @42
    @4
    cI
    fvexd
    @24
    @26
    @5
    cvv
    cvv
    cvv
    prsshashgt1
    syl31anc
    adantl
    sylbid
    mpdan
    ralimdva
    ex
    com23
    exp31
    com24
    3impia
    exp4c
    imp
    a1i
    sylbid
    com24
    com14
    3imp
    com12
    sylbid
    3ad2ant1
    mpcom
    pm2.43i
    imp
end
