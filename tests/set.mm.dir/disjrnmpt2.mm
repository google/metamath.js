include "crn.mm"
include "cv.mm"
include "wdisj.mm"
include "wn.mm"
include "wne.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "id.mm"
include "cbvdisjv.mm"
include "notbii.mm"
include "ndisj2.mm"
include "biimpi.mm"
include "sylbi.mm"
include "wcel.mm"
include "wi.mm"
include "elrnmpt.mm"
include "ibi.mm"
include "adantr.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "adantl.mm"
include "jca.mm"
include "nfv.mm"
include "nfeq.mm"
include "reean.mm"
include "sylibr.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfcri.mm"
include "nfan.mm"
include "simpll.mm"
include "eqcomd.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "adantll.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "adantlr.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ineq12d.mm"
include "simpl.mm"
include "eqnetrd.mm"
include "ex.mm"
include "reximdv.mm"
include "a1d.mm"
include "reximdai.mm"
include "mpd.mm"
include "a1i.mm"
include "rexlimdvv.mm"
include "cbvdisj.mm"
include "csbco.mm"
include "eqtrd.mm"
include "nfin.mm"
include "nfne.mm"
include "nfrex.mm"
include "neeq1.mm"
include "csbeq1.mm"
include "csbid.mm"
include "ineq1d.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "cbvrex.mm"
include "bitri.mm"
include "con4i.mm"

theorem disjrnmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vu: setvar u
  let vz: setvar z
  let vv: setvar v
  let vw: setvar w
  assume disjrnmpt2.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint F y
  disjoint A u
  disjoint A z
  disjoint u x
  disjoint u z
  disjoint x z
  disjoint A v
  disjoint A w
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint B u
  disjoint B z
  disjoint B v
  disjoint B w
  disjoint F v
  disjoint F w
  disjoint v y
  disjoint w y
  disjoint F z
  assert |- ( Disj_ x e. A B -> Disj_ y e. ran F y )

  proof
    vy
    cF
    crn
    #
    vy
    cv
    #
    wdisj
    #
    vx
    cA
    cB
    wdisj
    #
    @2
    wn
    #
    vx
    cv
    #
    vz
    cv
    #
    wne
    #
    cB
    vx
    @6
    cB
    csb
    #
    cin
    #
    c0
    wne
    #
    wa
    #
    vz
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    @3
    wn
    #
    @4
    vw
    cv
    #
    vv
    cv
    #
    wne
    #
    @15
    @16
    cin
    #
    c0
    wne
    #
    wa
    #
    vv
    @0
    wrex
    vw
    @0
    wrex
    #
    @13
    @4
    vw
    @0
    @15
    wdisj
    #
    wn
    #
    @21
    @2
    @22
    vy
    vw
    @0
    @1
    @15
    @1
    @15
    wceq
    id
    cbvdisjv
    notbii
    @23
    @21
    vw
    vv
    @0
    @15
    @16
    @15
    @16
    wceq
    #
    id
    ndisj2
    biimpi
    sylbi
    @4
    @20
    @13
    vw
    vv
    @0
    @0
    @15
    @0
    wcel
    #
    @16
    @0
    wcel
    #
    wa
    #
    @20
    @13
    wi
    wi
    @4
    @27
    @20
    @13
    @27
    @20
    wa
    #
    @15
    cB
    wceq
    #
    @16
    @8
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    @13
    @27
    @33
    @20
    @27
    @29
    vx
    cA
    wrex
    #
    @30
    vz
    cA
    wrex
    #
    wa
    @33
    @27
    @34
    @35
    @25
    @34
    @26
    @25
    @34
    vx
    cA
    cB
    @15
    cF
    @0
    disjrnmpt2.1
    elrnmpt
    ibi
    adantr
    @26
    @35
    @25
    @26
    @35
    vz
    cA
    @8
    @16
    cF
    @0
    cF
    vx
    cA
    cB
    cmpt
    #
    vz
    cA
    @8
    cmpt
    disjrnmpt2.1
    vx
    vz
    cA
    cB
    @8
    vz
    cB
    nfcv
    vx
    @6
    cB
    nfcsb1v
    #
    vx
    @6
    cB
    csbeq1a
    #
    cbvmpt
    eqtri
    elrnmpt
    ibi
    adantl
    jca
    @29
    @30
    vx
    vz
    cA
    cA
    @29
    vz
    nfv
    vx
    @16
    @8
    vx
    @16
    nfcv
    @37
    nfeq
    reean
    sylibr
    adantr
    @28
    @32
    @12
    vx
    cA
    @27
    @20
    vx
    @25
    @26
    vx
    vx
    @15
    @0
    vx
    @15
    nfcv
    vx
    cF
    vx
    cF
    @36
    disjrnmpt2.1
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    nfrn
    #
    nfel
    vx
    vv
    @0
    @39
    nfcri
    nfan
    @20
    vx
    nfv
    nfan
    @28
    @32
    @12
    wi
    @5
    cA
    wcel
    @28
    @31
    @11
    vz
    cA
    @20
    @31
    @11
    wi
    @27
    @20
    @31
    @11
    @20
    @31
    wa
    @7
    @10
    @17
    @31
    @7
    @19
    @17
    @31
    wa
    #
    @5
    @6
    @40
    @5
    @6
    wceq
    #
    @24
    @31
    @41
    @24
    @17
    @31
    @41
    wa
    @15
    cB
    @8
    @16
    @29
    @30
    @41
    simpll
    @41
    cB
    @8
    wceq
    @31
    @38
    adantl
    @30
    @8
    @16
    wceq
    #
    @29
    @41
    @30
    @16
    @8
    @30
    id
    eqcomd
    #
    ad2antlr
    3eqtrd
    adantll
    @40
    @41
    wa
    @15
    @16
    @17
    @31
    @41
    simpll
    neneqd
    pm2.65da
    neqned
    adantlr
    @19
    @31
    @10
    @17
    @19
    @31
    wa
    #
    @9
    @18
    c0
    @44
    cB
    @15
    @8
    @16
    @29
    cB
    @15
    wceq
    @19
    @30
    @29
    @15
    cB
    @29
    id
    eqcomd
    ad2antrl
    @30
    @42
    @19
    @29
    @43
    ad2antll
    ineq12d
    @19
    @31
    simpl
    eqnetrd
    adantll
    jca
    ex
    adantl
    reximdv
    a1d
    reximdai
    mpd
    ex
    a1i
    rexlimdvv
    mpd
    @14
    vu
    cA
    vx
    vu
    cv
    #
    cB
    csb
    #
    wdisj
    #
    wn
    #
    @13
    @3
    @47
    vx
    vu
    cA
    cB
    @46
    vu
    cB
    nfcv
    vx
    @45
    cB
    nfcsb1v
    #
    vx
    @45
    cB
    csbeq1a
    cbvdisj
    notbii
    @48
    @45
    @6
    wne
    #
    @46
    @8
    cin
    #
    c0
    wne
    #
    wa
    #
    vz
    cA
    wrex
    #
    vu
    cA
    wrex
    @13
    vu
    vz
    cA
    @46
    @8
    @45
    @6
    wceq
    #
    @46
    vu
    @6
    @46
    csb
    #
    @8
    vu
    @6
    @46
    csbeq1a
    @56
    @8
    wceq
    @55
    vx
    vu
    @6
    cB
    csbco
    a1i
    eqtrd
    ndisj2
    @54
    @12
    vu
    vx
    cA
    @53
    vx
    vz
    cA
    vx
    cA
    nfcv
    @50
    @52
    vx
    @50
    vx
    nfv
    vx
    @51
    c0
    vx
    @46
    @8
    @49
    @37
    nfin
    vx
    c0
    nfcv
    nfne
    nfan
    nfrex
    @12
    vu
    nfv
    @45
    @5
    wceq
    #
    @53
    @11
    vz
    cA
    @57
    @50
    @7
    @52
    @10
    @45
    @5
    @6
    neeq1
    @57
    @51
    @9
    c0
    @57
    @46
    cB
    @8
    @57
    @46
    vx
    @5
    cB
    csb
    #
    cB
    vx
    @45
    @5
    cB
    csbeq1
    @58
    cB
    wceq
    @57
    vx
    cB
    csbid
    a1i
    eqtrd
    ineq1d
    neeq1d
    anbi12d
    rexbidv
    cbvrex
    bitri
    bitri
    sylibr
    con4i
end
