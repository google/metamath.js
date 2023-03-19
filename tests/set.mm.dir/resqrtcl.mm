include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "csqrt.mm"
include "cfv.mm"
include "resqrex.mm"
include "w3a.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "cc.mm"
include "crio.mm"
include "simp1l.mm"
include "recn.mm"
include "sqrtval.mm"
include "3syl.mm"
include "simp3r.mm"
include "simp3l.mm"
include "rere.mm"
include "3ad2ant2.mm"
include "breqtrrd.mm"
include "rennim.mm"
include "3jca.mm"
include "wreu.mm"
include "wb.mm"
include "resqreu.mm"
include "3ad2ant1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "neleq1.mm"
include "syl.mm"
include "3anbi123d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem resqrtcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( sqrt ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cc0
    vy
    cv
    #
    cle
    wbr
    #
    @3
    c2
    cexp
    co
    #
    cA
    wceq
    #
    wa
    #
    vy
    cr
    wrex
    cA
    csqrt
    cfv
    #
    cr
    wcel
    #
    vy
    cA
    resqrex
    @2
    @7
    @9
    vy
    cr
    @2
    @3
    cr
    wcel
    #
    @7
    w3a
    #
    @8
    @3
    cr
    @11
    @8
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cc0
    @12
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @12
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    vx
    cc
    crio
    #
    @3
    @11
    @0
    cA
    cc
    wcel
    @8
    @20
    wceq
    @0
    @1
    @10
    @7
    simp1l
    cA
    recn
    vx
    cA
    sqrtval
    3syl
    @11
    @6
    cc0
    @3
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @3
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    @20
    @3
    wceq
    #
    @11
    @6
    @22
    @24
    @2
    @10
    @4
    @6
    simp3r
    @11
    cc0
    @3
    @21
    cle
    @2
    @10
    @4
    @6
    simp3l
    @10
    @2
    @21
    @3
    wceq
    @7
    @3
    rere
    3ad2ant2
    breqtrrd
    @10
    @2
    @24
    @7
    @3
    rennim
    3ad2ant2
    3jca
    @11
    @3
    cc
    wcel
    #
    @19
    vx
    cc
    wreu
    #
    @25
    @26
    wb
    @10
    @2
    @27
    @7
    @3
    recn
    3ad2ant2
    @2
    @10
    @28
    @7
    vx
    cA
    resqreu
    3ad2ant1
    @19
    @25
    vx
    cc
    @3
    @12
    @3
    wceq
    #
    @14
    @6
    @16
    @22
    @18
    @24
    @29
    @13
    @5
    cA
    @12
    @3
    c2
    cexp
    oveq1
    eqeq1d
    @29
    @15
    @21
    cc0
    cle
    @12
    @3
    cre
    fveq2
    breq2d
    @29
    @17
    @23
    wceq
    @18
    @24
    wb
    @12
    @3
    ci
    cmul
    oveq2
    @17
    @23
    crp
    neleq1
    syl
    3anbi123d
    riota2
    syl2anc
    mpbid
    eqtrd
    @2
    @10
    @7
    simp2
    eqeltrd
    rexlimdv3a
    mpd
end
