include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cltp.mm"
include "wbr.mm"
include "wral.mm"
include "cnp.mm"
include "wrex.mm"
include "wa.mm"
include "cuni.mm"
include "wpss.mm"
include "cnq.mm"
include "cltq.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "ltrelpr.mm"
include "brel.mm"
include "simpld.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "rexlimivw.mm"
include "adantl.mm"
include "wex.mm"
include "n0.mm"
include "ssel.mm"
include "prn0.mm"
include "0pss.mm"
include "elssuni.mm"
include "psssstr.mm"
include "syl2an.mm"
include "expcom.mm"
include "sylcom.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "prpssnq.mm"
include "ltprord.mm"
include "pssss.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "unissb.mm"
include "sspsstr.mm"
include "syl2im.mm"
include "rexlimdva.mm"
include "anim12d.mm"
include "prcdnq.mm"
include "ex.mm"
include "com3r.mm"
include "sylan9.mm"
include "reximdvai.mm"
include "eluni2.mm"
include "3imtr4g.mm"
include "com23.mm"
include "alrimdv.mm"
include "eluni.mm"
include "prnmax.mm"
include "syl6.mm"
include "imp.mm"
include "ssrexv.mm"
include "syl.mm"
include "expimpd.mm"
include "jcad.mm"
include "ralrimiv.mm"
include "elnp.mm"
include "sylanbrc.mm"

theorem suplem1pr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( A =/= (/) /\ E. x e. P. A. y e. A y <P x ) -> U. A e. P. )

  proof
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cltp
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cnp
    wrex
    #
    wa
    #
    c0
    cA
    cuni
    #
    wpss
    #
    @7
    cnq
    wpss
    #
    wa
    #
    @1
    @2
    cltq
    wbr
    #
    @1
    @7
    wcel
    #
    wi
    #
    vy
    wal
    #
    @2
    @1
    cltq
    wbr
    #
    vy
    @7
    wrex
    #
    wa
    #
    vx
    @7
    wral
    #
    @7
    cnp
    wcel
    cA
    cnp
    wss
    #
    @6
    @10
    @5
    @19
    @0
    @4
    @19
    vx
    cnp
    @4
    @1
    cnp
    wcel
    #
    vy
    cA
    wral
    @19
    @3
    @20
    vy
    cA
    @3
    @20
    @2
    cnp
    wcel
    #
    @1
    @2
    cnp
    cnp
    cltp
    ltrelpr
    brel
    #
    simpld
    ralimi
    vy
    cA
    cnp
    dfss3
    sylibr
    rexlimivw
    adantl
    #
    @19
    @0
    @8
    @5
    @9
    @0
    vz
    cv
    #
    cA
    wcel
    #
    vz
    wex
    @19
    @8
    vz
    cA
    n0
    @19
    @25
    @8
    vz
    @19
    @25
    @24
    cnp
    wcel
    #
    @8
    cA
    cnp
    @24
    ssel
    #
    @26
    @25
    @8
    @26
    c0
    @24
    wpss
    #
    @24
    @7
    wss
    #
    @8
    @25
    @26
    @24
    c0
    wne
    @28
    @24
    prn0
    @24
    0pss
    sylibr
    @24
    cA
    elssuni
    #
    c0
    @24
    @7
    psssstr
    syl2an
    expcom
    sylcom
    exlimdv
    syl5bi
    @19
    @4
    @9
    vx
    cnp
    @19
    @21
    wa
    @2
    cnq
    wpss
    #
    @4
    @7
    @2
    wss
    #
    @9
    @21
    @31
    @19
    @2
    prpssnq
    adantl
    @4
    @1
    @2
    wss
    #
    vy
    cA
    wral
    @32
    @3
    @33
    vy
    cA
    @20
    @21
    wa
    #
    @3
    @33
    @22
    @34
    @3
    @1
    @2
    wpss
    @33
    @1
    @2
    ltprord
    @1
    @2
    pssss
    syl6bi
    mpcom
    ralimi
    vy
    cA
    @2
    unissb
    sylibr
    @32
    @31
    @9
    @7
    @2
    cnq
    sspsstr
    expcom
    syl2im
    rexlimdva
    anim12d
    mpcom
    @6
    @19
    @18
    @23
    @19
    @17
    vx
    @7
    @19
    @2
    @7
    wcel
    #
    @14
    @16
    @19
    @35
    @13
    vy
    @19
    @11
    @35
    @12
    @19
    @11
    @35
    @12
    wi
    @19
    @11
    wa
    #
    @2
    @24
    wcel
    #
    vz
    cA
    wrex
    @1
    @24
    wcel
    #
    vz
    cA
    wrex
    @35
    @12
    @36
    @37
    @38
    vz
    cA
    @19
    @25
    @26
    @11
    @37
    @38
    wi
    @27
    @26
    @37
    @11
    @38
    @26
    @37
    @11
    @38
    wi
    @24
    @2
    @1
    prcdnq
    ex
    com3r
    sylan9
    reximdvai
    vz
    @2
    cA
    eluni2
    vz
    @1
    cA
    eluni2
    3imtr4g
    ex
    com23
    alrimdv
    @35
    @37
    @25
    wa
    #
    vz
    wex
    @19
    @16
    vz
    @2
    cA
    eluni
    @19
    @39
    @16
    vz
    @19
    @37
    @25
    @16
    @19
    @37
    wa
    @25
    @15
    vy
    @24
    wrex
    #
    @16
    @19
    @37
    @25
    @40
    wi
    @19
    @25
    @37
    @40
    @19
    @25
    @26
    @37
    @40
    wi
    @27
    @26
    @37
    @40
    vy
    @24
    @2
    prnmax
    ex
    syl6
    com23
    imp
    @25
    @29
    @40
    @16
    wi
    @30
    @15
    vy
    @24
    @7
    ssrexv
    syl
    sylcom
    expimpd
    exlimdv
    syl5bi
    jcad
    ralrimiv
    syl
    vx
    vy
    @7
    elnp
    sylanbrc
end
