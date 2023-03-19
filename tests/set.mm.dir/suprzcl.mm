include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "w3a.mm"
include "clt.mm"
include "csup.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wcel.mm"
include "zssre.mm"
include "sstr.mm"
include "mpan2.mm"
include "suprcl.mm"
include "syl3an1.mm"
include "ltm1d.mm"
include "wb.mm"
include "peano2rem.mm"
include "syl.mm"
include "suprlub.mm"
include "mpdan.mm"
include "mpbid.mm"
include "wa.mm"
include "wceq.mm"
include "caddc.mm"
include "simpl1.mm"
include "sselda.mm"
include "sseldi.mm"
include "adantr.mm"
include "simprl.mm"
include "sseldd.mm"
include "zre.mm"
include "peano2re.mm"
include "suprub.mm"
include "syl3anl1.mm"
include "adantlr.mm"
include "simprr.mm"
include "1red.mm"
include "ltsubaddd.mm"
include "lelttrd.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "suprleub.mm"
include "syldan.mm"
include "adantrr.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "rexlimddv.mm"

theorem suprzcl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( A C_ ZZ /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) -> sup ( A , RR , < ) e. A )

  proof
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    cA
    cr
    clt
    csup
    #
    c1
    cmin
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    @4
    cA
    wcel
    vz
    cA
    @3
    @5
    @4
    clt
    wbr
    #
    @7
    vz
    cA
    wrex
    #
    @3
    @4
    @0
    cA
    cr
    wss
    #
    @1
    @2
    @4
    cr
    wcel
    #
    @0
    cz
    cr
    wss
    @10
    zssre
    cA
    cz
    cr
    sstr
    mpan2
    #
    vx
    vy
    cA
    suprcl
    #
    syl3an1
    #
    ltm1d
    @0
    @10
    @1
    @2
    @8
    @9
    wb
    #
    @12
    @10
    @1
    @2
    w3a
    #
    @5
    cr
    wcel
    #
    @15
    @16
    @11
    @17
    @13
    @4
    peano2rem
    syl
    vx
    vy
    vz
    cA
    @5
    suprlub
    mpdan
    syl3an1
    mpbid
    @3
    @6
    cA
    wcel
    #
    @7
    wa
    #
    wa
    #
    @4
    @6
    cA
    @20
    @4
    @6
    wceq
    @4
    @6
    cle
    wbr
    #
    @6
    @4
    cle
    wbr
    #
    @20
    @21
    vw
    cv
    #
    @6
    cle
    wbr
    #
    vw
    cA
    wral
    #
    @20
    @24
    vw
    cA
    @20
    @23
    cA
    wcel
    #
    wa
    #
    @24
    @23
    @6
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @27
    @23
    @4
    @28
    @27
    cz
    cr
    @23
    zssre
    @20
    cA
    cz
    @23
    @0
    @1
    @2
    @19
    simpl1
    #
    sselda
    #
    sseldi
    @20
    @11
    @26
    @3
    @11
    @19
    @14
    adantr
    #
    adantr
    @20
    @28
    cr
    wcel
    #
    @26
    @20
    @6
    cr
    wcel
    #
    @33
    @20
    @6
    cz
    wcel
    #
    @34
    @20
    cA
    cz
    @6
    @30
    @3
    @18
    @7
    simprl
    #
    sseldd
    #
    @6
    zre
    syl
    #
    @6
    peano2re
    syl
    adantr
    @3
    @26
    @23
    @4
    cle
    wbr
    #
    @19
    @0
    @10
    @1
    @2
    @26
    @39
    @12
    vx
    vy
    cA
    @23
    suprub
    syl3anl1
    adantlr
    @20
    @4
    @28
    clt
    wbr
    #
    @26
    @20
    @7
    @40
    @3
    @18
    @7
    simprr
    @20
    @4
    c1
    @6
    @32
    @20
    1red
    @38
    ltsubaddd
    mpbid
    adantr
    lelttrd
    @27
    @23
    cz
    wcel
    @35
    @24
    @29
    wb
    @31
    @20
    @35
    @26
    @37
    adantr
    @23
    @6
    zleltp1
    syl2anc
    mpbird
    ralrimiva
    @3
    @19
    @34
    @21
    @25
    wb
    #
    @38
    @0
    @10
    @1
    @2
    @34
    @41
    @12
    vx
    vy
    vw
    cA
    @6
    suprleub
    syl3anl1
    syldan
    mpbird
    @3
    @18
    @22
    @7
    @0
    @10
    @1
    @2
    @18
    @22
    @12
    vx
    vy
    cA
    @6
    suprub
    syl3anl1
    adantrr
    @20
    @4
    @6
    @32
    @38
    letri3d
    mpbir2and
    @36
    eqeltrd
    rexlimddv
end
