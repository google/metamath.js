include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "clcm.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "lcmn0val.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "wrex.mm"
include "cmul.mm"
include "cabs.mm"
include "zmulcl.mm"
include "adantr.mm"
include "cc.mm"
include "zcn.mm"
include "anim12i.mm"
include "ioran.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "sylbb2.mm"
include "mulne0.mm"
include "an4s.mm"
include "syl2an.mm"
include "nnabscl.mm"
include "syl2anc.mm"
include "dvdsmul1.mm"
include "wb.mm"
include "dvdsabsb.mm"
include "syldan.mm"
include "mpbid.mm"
include "dvdsmul2.mm"
include "sylan2.mm"
include "anabss7.mm"
include "jca.mm"
include "breq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem lcmcllem
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cK: class K

  disjoint M n
  disjoint N n
  disjoint K n
  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 \/ N = 0 ) ) -> ( M lcm N ) e. { n e. NN | ( M || n /\ N || n ) } )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
    wn
    #
    wa
    #
    cM
    cN
    clcm
    co
    cM
    vn
    cv
    #
    cdvds
    wbr
    #
    cN
    @7
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    @11
    vn
    cM
    cN
    lcmn0val
    @6
    @11
    c1
    cuz
    cfv
    #
    wss
    @11
    c0
    wne
    #
    @12
    @11
    wcel
    @11
    cn
    @13
    @10
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    @6
    @10
    vn
    cn
    wrex
    #
    @14
    @6
    cM
    cN
    cmul
    co
    #
    cabs
    cfv
    #
    cn
    wcel
    #
    cM
    @17
    cdvds
    wbr
    #
    cN
    @17
    cdvds
    wbr
    #
    wa
    #
    @15
    @6
    @16
    cz
    wcel
    #
    @16
    cc0
    wne
    #
    @18
    @2
    @22
    @5
    cM
    cN
    zmulcl
    #
    adantr
    @2
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    wa
    cM
    cc0
    wne
    #
    cN
    cc0
    wne
    #
    wa
    #
    @23
    @5
    @0
    @25
    @1
    @26
    cM
    zcn
    cN
    zcn
    anim12i
    @5
    @3
    wn
    #
    @4
    wn
    #
    wa
    @29
    @3
    @4
    ioran
    @27
    @30
    @28
    @31
    cM
    cc0
    df-ne
    cN
    cc0
    df-ne
    anbi12i
    sylbb2
    @25
    @27
    @26
    @28
    @23
    cM
    cN
    mulne0
    an4s
    syl2an
    @16
    nnabscl
    syl2anc
    @2
    @21
    @5
    @2
    @19
    @20
    @2
    cM
    @16
    cdvds
    wbr
    #
    @19
    cM
    cN
    dvdsmul1
    @0
    @1
    @22
    @32
    @19
    wb
    @24
    cM
    @16
    dvdsabsb
    syldan
    mpbid
    @2
    cN
    @16
    cdvds
    wbr
    #
    @20
    cM
    cN
    dvdsmul2
    @0
    @1
    @33
    @20
    wb
    #
    @2
    @1
    @22
    @34
    @24
    cN
    @16
    dvdsabsb
    sylan2
    anabss7
    mpbid
    jca
    adantr
    @10
    @21
    vn
    @17
    cn
    @7
    @17
    wceq
    @8
    @19
    @9
    @20
    @7
    @17
    cM
    cdvds
    breq2
    @7
    @17
    cN
    cdvds
    breq2
    anbi12d
    rspcev
    syl2anc
    @10
    vn
    cn
    rabn0
    sylibr
    @11
    c1
    infssuzcl
    sylancr
    eqeltrd
end
