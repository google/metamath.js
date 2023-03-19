include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "w3a.mm"
include "wi.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "a1i.mm"
include "cn.mm"
include "eluz2nn.mm"
include "adantr.mm"
include "prmdvdsfi.mm"
include "syl.mm"
include "wrex.mm"
include "exprmfct.mm"
include "rabn0.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "prmssnn.mm"
include "nnssre.mm"
include "sstri.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "eleq1i.mm"
include "adantl.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfinf.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "breq1.mm"
include "elrabf.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp1r.mm"
include "wb.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "3jca.mm"
include "3exp.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "syl5bir.mm"
include "mpd.mm"

theorem prmdvdsfmtnof1lem1
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume prmdvdsfmtnof1lem1.i: |- I = inf ( { p e. Prime | p || F } , RR , < )
  assume prmdvdsfmtnof1lem1.j: |- J = inf ( { p e. Prime | p || G } , RR , < )

  disjoint F p
  disjoint G p
  disjoint k x
  assert |- ( ( F e. ( ZZ>= ` 2 ) /\ G e. ( ZZ>= ` 2 ) ) -> ( I = J -> ( I e. Prime /\ I || F /\ I || G ) ) )

  proof
    cF
    c2
    cuz
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    vp
    cv
    #
    cF
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    clt
    cinf
    #
    @6
    wcel
    #
    cI
    cJ
    wceq
    #
    cI
    cprime
    wcel
    #
    cI
    cF
    cdvds
    wbr
    #
    cI
    cG
    cdvds
    wbr
    #
    w3a
    #
    wi
    #
    @3
    cr
    clt
    wor
    #
    @6
    cfn
    wcel
    #
    @6
    c0
    wne
    #
    @6
    cr
    wss
    #
    @8
    @15
    @3
    ltso
    a1i
    #
    @3
    cF
    cn
    wcel
    #
    @16
    @1
    @20
    @2
    cF
    eluz2nn
    adantr
    cF
    vp
    prmdvdsfi
    syl
    @3
    @5
    vp
    cprime
    wrex
    #
    @17
    @1
    @21
    @2
    cF
    vp
    exprmfct
    adantr
    @5
    vp
    cprime
    rabn0
    sylibr
    @18
    @3
    @6
    cprime
    cr
    @5
    vp
    cprime
    ssrab2
    cprime
    cn
    cr
    prmssnn
    nnssre
    sstri
    #
    sstri
    a1i
    cr
    @6
    clt
    fiinfcl
    syl13anc
    @8
    cI
    @6
    wcel
    #
    @3
    @14
    cI
    @7
    @6
    prmdvdsfmtnof1lem1.i
    eleq1i
    @3
    @4
    cG
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    clt
    cinf
    #
    @25
    wcel
    #
    @23
    @14
    wi
    #
    @3
    @15
    @25
    cfn
    wcel
    #
    @25
    c0
    wne
    #
    @25
    cr
    wss
    #
    @27
    @19
    @3
    cG
    cn
    wcel
    #
    @29
    @2
    @32
    @1
    cG
    eluz2nn
    adantl
    cG
    vp
    prmdvdsfi
    syl
    @3
    @24
    vp
    cprime
    wrex
    #
    @30
    @2
    @33
    @1
    cG
    vp
    exprmfct
    adantl
    @24
    vp
    cprime
    rabn0
    sylibr
    @31
    @3
    @25
    cprime
    cr
    @24
    vp
    cprime
    ssrab2
    @22
    sstri
    a1i
    cr
    @25
    clt
    fiinfcl
    syl13anc
    @27
    cJ
    @25
    wcel
    #
    @3
    @28
    cJ
    @26
    @25
    prmdvdsfmtnof1lem1.j
    eleq1i
    @34
    @28
    wi
    @3
    @34
    cJ
    cprime
    wcel
    #
    cJ
    cG
    cdvds
    wbr
    #
    wa
    #
    @28
    @24
    @36
    vp
    cJ
    cprime
    vp
    cJ
    @26
    prmdvdsfmtnof1lem1.j
    vp
    @25
    cr
    clt
    @24
    vp
    cprime
    nfrab1
    vp
    cr
    nfcv
    #
    vp
    clt
    nfcv
    #
    nfinf
    nfcxfr
    #
    vp
    cprime
    nfcv
    #
    vp
    cJ
    cG
    cdvds
    @40
    vp
    cdvds
    nfcv
    #
    vp
    cG
    nfcv
    nfbr
    @4
    cJ
    cG
    cdvds
    breq1
    elrabf
    @23
    @10
    @11
    wa
    #
    @37
    @14
    @5
    @11
    vp
    cI
    cprime
    vp
    cI
    @7
    prmdvdsfmtnof1lem1.i
    vp
    @6
    cr
    clt
    @5
    vp
    cprime
    nfrab1
    @38
    @39
    nfinf
    nfcxfr
    #
    @41
    vp
    cI
    cF
    cdvds
    @44
    @42
    vp
    cF
    nfcv
    nfbr
    @4
    cI
    cF
    cdvds
    breq1
    elrabf
    @37
    @43
    @9
    @13
    @37
    @43
    @9
    w3a
    #
    @10
    @11
    @12
    @37
    @10
    @11
    @9
    simp2l
    @37
    @10
    @11
    @9
    simp2r
    @45
    @12
    @36
    @35
    @36
    @43
    @9
    simp1r
    @9
    @37
    @12
    @36
    wb
    @43
    cI
    cJ
    cG
    cdvds
    breq1
    3ad2ant3
    mpbird
    3jca
    3exp
    syl5bi
    sylbi
    a1i
    syl5bir
    mpd
    syl5bir
    mpd
end
