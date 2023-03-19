include "csuc.mm"
include "ccmp.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "cvv.mm"
include "elex.mm"
include "sucexb.mm"
include "sylibr.mm"
include "wss.mm"
include "sssucid.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "wlim.mm"
include "limuni.mm"
include "ax-mp.mm"
include "wne.mm"
include "elin.mm"
include "elpwi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "c0.mm"
include "wb.mm"
include "nlim0.mm"
include "2th.mm"
include "xor3.mm"
include "mpbir.mm"
include "limeq.mm"
include "necon3bi.mm"
include "uni0.mm"
include "neeqtrri.mm"
include "unieq.mm"
include "neeq2d.mm"
include "a1i.mm"
include "con0.mm"
include "word.mm"
include "limord.mm"
include "ordsson.mm"
include "mp2b.mm"
include "sstr2.mm"
include "mpi.mm"
include "ordunifi.mm"
include "3expia.mm"
include "sylan.mm"
include "ssel.mm"
include "nordeq.mm"
include "mpan.mm"
include "syl6.mm"
include "adantr.mm"
include "syld.mm"
include "pm2.61dne.mm"
include "syl.mm"
include "neneqd.mm"
include "nrex.mm"
include "eqeq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr12.mm"
include "rexanali.mm"
include "sylib.mm"
include "3syl.mm"
include "imnan.mm"
include "mpbi.mm"
include "ordunisuc.mm"
include "eqcomi.mm"
include "iscmp.mm"
include "mtbir.mm"

theorem limsucncmpi
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume limsucncmpi.1: |- Lim A


  assert |- -. suc A e. Comp

  proof
    cA
    csuc
    #
    ccmp
    wcel
    @0
    ctop
    wcel
    #
    cA
    vy
    cv
    #
    cuni
    #
    wceq
    #
    cA
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    @2
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    vy
    @0
    cpw
    #
    wral
    #
    wa
    #
    @1
    @12
    wn
    #
    wi
    @13
    wn
    @1
    cA
    cvv
    wcel
    #
    cA
    @11
    wcel
    #
    @14
    @1
    @0
    cvv
    wcel
    @15
    @0
    ctop
    elex
    cA
    sucexb
    sylibr
    @15
    @16
    cA
    @0
    wss
    cA
    sssucid
    cA
    @0
    cvv
    elpwg
    mpbiri
    @16
    @4
    @10
    wn
    #
    wa
    #
    vy
    @11
    wrex
    #
    @14
    @16
    cA
    cA
    cuni
    #
    wceq
    #
    @7
    vz
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wn
    #
    @19
    cA
    wlim
    #
    @21
    limsucncmpi.1
    cA
    limuni
    ax-mp
    @7
    vz
    @23
    @5
    @23
    wcel
    #
    cA
    @6
    @27
    @5
    cA
    wss
    #
    @5
    cfn
    wcel
    #
    wa
    #
    cA
    @6
    wne
    #
    @27
    @5
    @22
    wcel
    #
    @29
    wa
    @30
    @5
    @22
    cfn
    elin
    @32
    @28
    @29
    @5
    cA
    elpwi
    anim1i
    sylbi
    @30
    @31
    @5
    c0
    @5
    c0
    wceq
    #
    @31
    wi
    @30
    @33
    @31
    cA
    c0
    cuni
    #
    wne
    cA
    c0
    @34
    @26
    c0
    wlim
    #
    wb
    #
    wn
    #
    cA
    c0
    wne
    @37
    @26
    @35
    wn
    #
    wb
    @26
    @38
    limsucncmpi.1
    nlim0
    2th
    @26
    @35
    xor3
    mpbir
    @36
    cA
    c0
    cA
    c0
    limeq
    necon3bi
    ax-mp
    uni0
    neeqtrri
    @33
    @6
    @34
    cA
    @5
    c0
    unieq
    neeq2d
    mpbiri
    a1i
    @30
    @5
    c0
    wne
    #
    @6
    @5
    wcel
    #
    @31
    @28
    @5
    con0
    wss
    #
    @29
    @39
    @40
    wi
    @28
    cA
    con0
    wss
    #
    @41
    @26
    cA
    word
    #
    @42
    limsucncmpi.1
    cA
    limord
    #
    cA
    ordsson
    mp2b
    @5
    cA
    con0
    sstr2
    mpi
    @41
    @29
    @39
    @40
    @5
    ordunifi
    3expia
    sylan
    @28
    @40
    @31
    wi
    @29
    @28
    @40
    @6
    cA
    wcel
    #
    @31
    @5
    cA
    @6
    ssel
    @43
    @45
    @31
    @26
    @43
    limsucncmpi.1
    @44
    ax-mp
    cA
    @6
    nordeq
    mpan
    syl6
    adantr
    syld
    pm2.61dne
    syl
    neneqd
    nrex
    @18
    @21
    @25
    wa
    vy
    cA
    @11
    @2
    cA
    wceq
    #
    @4
    @21
    @17
    @25
    @46
    @3
    @20
    cA
    @2
    cA
    unieq
    eqeq2d
    @46
    @10
    @24
    @46
    @7
    vz
    @9
    @23
    @46
    @8
    @22
    cfn
    @2
    cA
    pweq
    ineq1d
    rexeqdv
    notbid
    anbi12d
    rspcev
    mpanr12
    @4
    @10
    vy
    @11
    rexanali
    sylib
    3syl
    @1
    @12
    imnan
    mpbi
    vy
    vz
    @0
    cA
    @0
    cuni
    #
    cA
    @26
    @43
    @47
    cA
    wceq
    limsucncmpi.1
    @44
    cA
    ordunisuc
    mp2b
    eqcomi
    iscmp
    mtbir
end
