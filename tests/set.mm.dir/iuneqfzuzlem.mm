include "cv.mm"
include "cfz.mm"
include "co.mm"
include "ciun.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "csb.mm"
include "wrex.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "nfra1.mm"
include "nfv.mm"
include "w3a.mm"
include "simp2.mm"
include "rspa.mm"
include "3adant3.mm"
include "simp3.mm"
include "id.mm"
include "cuz.mm"
include "cfv.mm"
include "fzssuz.mm"
include "eqcomi.mm"
include "sseqtri.mm"
include "iunss1.mm"
include "mp1i.mm"
include "eqsstrd.mm"
include "3ad2ant2.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluzel2.mm"
include "syl.mm"
include "eluzelz.mm"
include "3jca.mm"
include "eluzle.mm"
include "cr.mm"
include "zred.mm"
include "leid.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "nfel.mm"
include "eleq2d.mm"
include "rspce.mm"
include "sylan.mm"
include "3adant2.mm"
include "sseldd.mm"
include "syl3anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "adantr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dfss3.mm"

theorem iuneqfzuzlem
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  assume iuneqfzuzlem.z: |- Z = ( ZZ>= ` N )

  disjoint A m
  disjoint B m
  disjoint N n
  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint A x
  disjoint m x
  disjoint B x
  disjoint N x
  disjoint n x
  disjoint Z x
  assert |- ( A. m e. Z U_ n e. ( N ... m ) A = U_ n e. ( N ... m ) B -> U_ n e. Z A C_ U_ n e. Z B )

  proof
    vn
    cN
    vm
    cv
    #
    cfz
    co
    #
    cA
    ciun
    #
    vn
    @1
    cB
    ciun
    #
    wceq
    #
    vm
    cZ
    wral
    #
    vx
    cv
    #
    vn
    cZ
    cB
    ciun
    #
    wcel
    #
    vx
    vn
    cZ
    cA
    ciun
    #
    wral
    @9
    @7
    wss
    @5
    @8
    vx
    @9
    @5
    @6
    @9
    wcel
    #
    wa
    @6
    vn
    @0
    cA
    csb
    #
    wcel
    #
    vm
    cZ
    wrex
    #
    @8
    @10
    @13
    @5
    @10
    @13
    @10
    @6
    vm
    cZ
    @11
    ciun
    #
    wcel
    @13
    @9
    @14
    @6
    vn
    vm
    cZ
    cA
    @11
    vm
    cA
    nfcv
    vn
    @0
    cA
    nfcsb1v
    #
    vn
    @0
    cA
    csbeq1a
    #
    cbviun
    eleq2i
    vm
    @6
    cZ
    @11
    eliun
    bitri
    biimpi
    adantl
    @5
    @13
    @8
    wi
    @10
    @5
    @12
    @8
    vm
    cZ
    @4
    vm
    cZ
    nfra1
    @8
    vm
    nfv
    @5
    @0
    cZ
    wcel
    #
    @12
    @8
    @5
    @17
    @12
    w3a
    @17
    @4
    @12
    @8
    @5
    @17
    @12
    simp2
    @5
    @17
    @4
    @12
    @4
    vm
    cZ
    rspa
    3adant3
    @5
    @17
    @12
    simp3
    @17
    @4
    @12
    w3a
    @2
    @7
    @6
    @4
    @17
    @2
    @7
    wss
    @12
    @4
    @2
    @3
    @7
    @4
    id
    @1
    cZ
    wss
    @3
    @7
    wss
    @4
    @1
    cN
    cuz
    cfv
    #
    cZ
    cN
    @0
    fzssuz
    cZ
    @18
    iuneqfzuzlem.z
    eqcomi
    sseqtri
    vn
    @1
    cZ
    cB
    iunss1
    mp1i
    eqsstrd
    3ad2ant2
    @17
    @12
    @6
    @2
    wcel
    #
    @4
    @17
    @12
    wa
    @6
    cA
    wcel
    #
    vn
    @1
    wrex
    #
    @19
    @17
    @0
    @1
    wcel
    #
    @12
    @21
    @17
    cN
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    @24
    w3a
    #
    cN
    @0
    cle
    wbr
    #
    @0
    @0
    cle
    wbr
    #
    wa
    wa
    @22
    @17
    @25
    @26
    @27
    @17
    @23
    @24
    @24
    @17
    @0
    @18
    wcel
    #
    @23
    @17
    @28
    cZ
    @18
    @0
    iuneqfzuzlem.z
    eleq2i
    biimpi
    #
    cN
    @0
    eluzel2
    syl
    @17
    @28
    @24
    @29
    cN
    @0
    eluzelz
    syl
    #
    @30
    3jca
    @17
    @28
    @26
    @29
    cN
    @0
    eluzle
    syl
    @17
    @0
    cr
    wcel
    @27
    @17
    @0
    @30
    zred
    @0
    leid
    syl
    jca32
    @0
    cN
    @0
    elfz2
    sylibr
    @20
    @12
    vn
    @0
    @1
    vn
    @6
    @11
    vn
    @6
    nfcv
    @15
    nfel
    vn
    cv
    @0
    wceq
    cA
    @11
    @6
    @16
    eleq2d
    rspce
    sylan
    vn
    @6
    @1
    cA
    eliun
    sylibr
    3adant2
    sseldd
    syl3anc
    3exp
    rexlimd
    adantr
    mpd
    ralrimiva
    vx
    @9
    @7
    dfss3
    sylibr
end
