include "crp.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cn.mm"
include "cppi.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cn0.mm"
include "rpre.mm"
include "ppicl.mm"
include "syl.mm"
include "nn0red.mm"
include "adantr.mm"
include "reflcl.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "c1.mm"
include "csdm.mm"
include "cfn.mm"
include "wpss.mm"
include "fzfi.mm"
include "wss.mm"
include "inss1.mm"
include "wne.mm"
include "cuz.mm"
include "2eluzge1.mm"
include "fzss1.mm"
include "mp1i.mm"
include "wn.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "cle.mm"
include "1lt2.mm"
include "1re.mm"
include "2re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "elfzle1.mm"
include "mto.mm"
include "nelne1.mm"
include "sylancl.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "sspsstr.mm"
include "sylancr.mm"
include "php3.mm"
include "wb.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashsdom.mm"
include "sylibr.mm"
include "cz.mm"
include "flcld.mm"
include "ppival2.mm"
include "ppifl.mm"
include "eqtr3d.mm"
include "rpge0.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "hashfz1.mm"
include "3brtr3d.mm"
include "flle.mm"
include "ltletrd.mm"
include "fveq2d.mm"
include "2pos.mm"
include "0re.mm"
include "ppieq0.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "syl6eq.mm"
include "rpgt0.mm"
include "eqbrtrd.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem ppiltx
  let cA: class A


  assert |- ( A e. RR+ -> ( ppi ` A ) < A )

  proof
    cA
    crp
    wcel
    #
    cA
    cfl
    cfv
    #
    cn
    wcel
    #
    cA
    cppi
    cfv
    #
    cA
    clt
    wbr
    @1
    cc0
    wceq
    #
    @0
    @2
    wa
    #
    @3
    @1
    cA
    @0
    @3
    cr
    wcel
    @2
    @0
    @3
    @0
    cA
    cr
    wcel
    #
    @3
    cn0
    wcel
    cA
    rpre
    #
    cA
    ppicl
    syl
    nn0red
    adantr
    @0
    @1
    cr
    wcel
    #
    @2
    @0
    @6
    @8
    @7
    cA
    reflcl
    syl
    adantr
    @0
    @6
    @2
    @7
    adantr
    #
    @5
    c2
    @1
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    c1
    @1
    cfz
    co
    #
    chash
    cfv
    #
    @3
    @1
    clt
    @5
    @11
    @13
    csdm
    wbr
    #
    @12
    @14
    clt
    wbr
    #
    @5
    @13
    cfn
    wcel
    #
    @11
    @13
    wpss
    #
    @15
    c1
    @1
    fzfi
    #
    @5
    @11
    @10
    wss
    #
    @10
    @13
    wpss
    #
    @18
    @10
    cprime
    inss1
    #
    @5
    @10
    @13
    wss
    #
    @10
    @13
    wne
    @21
    c2
    c1
    cuz
    cfv
    #
    wcel
    @23
    @5
    2eluzge1
    c2
    c1
    @1
    fzss1
    mp1i
    @5
    @13
    @10
    @5
    c1
    @13
    wcel
    #
    c1
    @10
    wcel
    #
    wn
    @13
    @10
    wne
    @5
    @1
    @24
    wcel
    @25
    @5
    @1
    cn
    @24
    @0
    @2
    simpr
    nnuz
    syl6eleq
    c1
    @1
    eluzfz1
    syl
    @26
    c2
    c1
    cle
    wbr
    #
    c1
    c2
    clt
    wbr
    @27
    wn
    1lt2
    c1
    c2
    1re
    2re
    ltnlei
    mpbi
    c1
    c2
    @1
    elfzle1
    mto
    c1
    @13
    @10
    nelne1
    sylancl
    necomd
    @10
    @13
    df-pss
    sylanbrc
    @11
    @10
    @13
    sspsstr
    sylancr
    @13
    @11
    php3
    sylancr
    @11
    cfn
    wcel
    #
    @17
    @16
    @15
    wb
    @10
    cfn
    wcel
    @20
    @28
    c2
    @1
    fzfi
    @22
    @10
    @11
    ssfi
    mp2an
    @19
    @11
    @13
    hashsdom
    mp2an
    sylibr
    @0
    @12
    @3
    wceq
    @2
    @0
    @1
    cppi
    cfv
    #
    @12
    @3
    @0
    @1
    cz
    wcel
    @29
    @12
    wceq
    @0
    cA
    @7
    flcld
    @1
    ppival2
    syl
    @0
    @6
    @29
    @3
    wceq
    #
    @7
    cA
    ppifl
    syl
    #
    eqtr3d
    adantr
    @0
    @14
    @1
    wceq
    #
    @2
    @0
    @1
    cn0
    wcel
    #
    @32
    @0
    @6
    cc0
    cA
    cle
    wbr
    @33
    @7
    cA
    rpge0
    cA
    flge0nn0
    syl2anc
    #
    @1
    hashfz1
    syl
    adantr
    3brtr3d
    @5
    @6
    @1
    cA
    cle
    wbr
    @9
    cA
    flle
    syl
    ltletrd
    @0
    @4
    wa
    #
    @3
    cc0
    cA
    clt
    @35
    @29
    @3
    cc0
    @0
    @30
    @4
    @31
    adantr
    @35
    @29
    cc0
    cppi
    cfv
    #
    cc0
    @35
    @1
    cc0
    cppi
    @0
    @4
    simpr
    fveq2d
    @36
    cc0
    wceq
    #
    cc0
    c2
    clt
    wbr
    #
    2pos
    cc0
    cr
    wcel
    @37
    @38
    wb
    0re
    cc0
    ppieq0
    ax-mp
    mpbir
    syl6eq
    eqtr3d
    @0
    cc0
    cA
    clt
    wbr
    @4
    cA
    rpgt0
    adantr
    eqbrtrd
    @0
    @33
    @2
    @4
    wo
    @34
    @1
    elnn0
    sylib
    mpjaodan
end
