include "wss.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "c0.mm"
include "cpr.mm"
include "topgele.mm"
include "adantl.mm"
include "simprd.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wex.mm"
include "selpw.mm"
include "w3a.mm"
include "csn.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "simp3.mm"
include "cmpt.mm"
include "crn.mm"
include "cima.mm"
include "cres.mm"
include "df-ima.mm"
include "resmpt.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "rnmptsn.mm"
include "syl6eq.mm"
include "imassrn.mm"
include "syl6eqssr.mm"
include "syl6sseq.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "abbii.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "wi.mm"
include "sstr.mm"
include "expcom.mm"
include "adantr.mm"
include "mpd.mm"
include "3adant3.mm"
include "ssexd.mm"
include "isset.mm"
include "sylib.mm"
include "eqid.mm"
include "mptsnun.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "jca.mm"
include "sseq1.mm"
include "unieq.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "eximdv.mm"
include "syl3an2b.mm"
include "3com23.mm"
include "3expia.mm"
include "wb.mm"
include "ctg.mm"
include "ctop.mm"
include "topontop.mm"
include "tgtop.mm"
include "syl.mm"
include "eleq2d.mm"
include "eltg3.mm"
include "bitr3d.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem dissneqlem
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  assume dissneq.c: |- C = { u | E. x e. A u = { x } }

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint B x
  disjoint C x
  disjoint A y
  disjoint A z
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint C y
  assert |- ( ( C C_ B /\ B e. ( TopOn ` A ) ) -> B = ~P A )

  proof
    cC
    cB
    wss
    #
    cB
    cA
    ctopon
    cfv
    #
    wcel
    #
    wa
    #
    cB
    cA
    cpw
    #
    @3
    c0
    cA
    cpr
    cB
    wss
    #
    cB
    @4
    wss
    #
    @2
    @5
    @6
    wa
    @0
    cB
    cA
    topgele
    adantl
    simprd
    @3
    vx
    @4
    cB
    @3
    vx
    cv
    #
    @4
    wcel
    #
    vy
    cv
    #
    cB
    wss
    #
    @7
    @9
    cuni
    #
    wceq
    #
    wa
    #
    vy
    wex
    #
    @7
    cB
    wcel
    #
    @0
    @2
    @8
    @14
    @0
    @8
    @2
    @14
    @8
    @0
    @7
    cA
    wss
    #
    @2
    @14
    vx
    cA
    selpw
    @0
    @16
    @2
    w3a
    #
    @9
    vu
    cv
    #
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    @7
    wrex
    vu
    cab
    #
    wceq
    #
    vy
    wex
    #
    @14
    @17
    @22
    cvv
    wcel
    @24
    @17
    @22
    cB
    @1
    @0
    @16
    @2
    simp3
    @0
    @16
    @22
    cB
    wss
    #
    @2
    @0
    @16
    wa
    #
    @22
    cC
    wss
    #
    @25
    @16
    @27
    @0
    @16
    @22
    @21
    vz
    cA
    wrex
    #
    vu
    cab
    #
    cC
    @16
    @22
    vz
    cA
    @20
    cmpt
    #
    crn
    #
    @29
    @16
    @22
    @30
    @7
    cima
    #
    @31
    @16
    @32
    vz
    @7
    @20
    cmpt
    #
    crn
    #
    @22
    @16
    @32
    @30
    @7
    cres
    #
    crn
    @34
    @30
    @7
    df-ima
    @16
    @35
    @33
    vz
    cA
    @7
    @20
    resmpt
    rneqd
    syl5eq
    vz
    vu
    @7
    rnmptsn
    syl6eq
    #
    @30
    @7
    imassrn
    syl6eqssr
    vz
    vu
    cA
    rnmptsn
    syl6sseq
    cC
    @18
    @7
    csn
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vu
    cab
    @29
    dissneq.c
    @39
    @28
    vu
    @38
    @21
    vx
    vz
    cA
    @7
    @19
    wceq
    @37
    @20
    @18
    @7
    @19
    sneq
    eqeq2d
    cbvrexv
    abbii
    eqtri
    syl6sseqr
    adantl
    @0
    @27
    @25
    wi
    @16
    @27
    @0
    @25
    @22
    cC
    cB
    sstr
    expcom
    adantr
    mpd
    #
    3adant3
    ssexd
    vy
    @22
    isset
    sylib
    @0
    @16
    @24
    @14
    wi
    @2
    @26
    @23
    @13
    vy
    @26
    @13
    @23
    @25
    @7
    @22
    cuni
    #
    wceq
    #
    wa
    @26
    @25
    @42
    @40
    @16
    @42
    @0
    @16
    @7
    @32
    cuni
    @41
    vz
    vu
    cA
    @7
    @29
    @30
    @30
    eqid
    @29
    eqid
    mptsnun
    @16
    @32
    @22
    @36
    unieqd
    eqtrd
    adantl
    jca
    @23
    @10
    @25
    @12
    @42
    @9
    @22
    cB
    sseq1
    @23
    @11
    @41
    @7
    @9
    @22
    unieq
    eqeq2d
    anbi12d
    syl5ibrcom
    eximdv
    3adant3
    mpd
    syl3an2b
    3com23
    3expia
    @2
    @15
    @14
    wb
    @0
    @2
    @7
    cB
    ctg
    cfv
    #
    wcel
    @15
    @14
    @2
    @43
    cB
    @7
    @2
    cB
    ctop
    wcel
    @43
    cB
    wceq
    cA
    cB
    topontop
    cB
    tgtop
    syl
    eleq2d
    vy
    @7
    cB
    @1
    eltg3
    bitr3d
    adantl
    sylibrd
    ssrdv
    eqssd
end
