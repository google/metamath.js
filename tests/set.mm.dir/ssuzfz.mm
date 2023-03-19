include "cv.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "sselda.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sstrd.mm"
include "adantr.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "ne0i.mm"
include "adantl.mm"
include "suprfinzcl.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "3jca.mm"
include "eluzle.mm"
include "zssre.mm"
include "simpr.mm"
include "eqidd.mm"
include "supfirege.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimiv.mm"
include "dfss3.mm"

theorem ssuzfz
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  assume ssuzfz.1: |- Z = ( ZZ>= ` M )
  assume ssuzfz.2: |- ( ph -> A C_ Z )
  assume ssuzfz.3: |- ( ph -> A e. Fin )


  assert |- ( ph -> A C_ ( M ... sup ( A , RR , < ) ) )

  proof
    wph
    vk
    cv
    #
    cM
    cA
    cr
    clt
    csup
    #
    cfz
    co
    #
    wcel
    #
    vk
    cA
    wral
    cA
    @2
    wss
    wph
    @3
    vk
    cA
    wph
    @0
    cA
    wcel
    #
    @3
    wph
    @4
    wa
    #
    cM
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    w3a
    #
    cM
    @0
    cle
    wbr
    #
    @0
    @1
    cle
    wbr
    #
    wa
    wa
    @3
    @5
    @9
    @10
    @11
    @5
    @6
    @7
    @8
    @5
    @0
    cM
    cuz
    cfv
    #
    wcel
    #
    @6
    @5
    @0
    cZ
    @12
    wph
    cA
    cZ
    @0
    ssuzfz.2
    sselda
    ssuzfz.1
    syl6eleq
    #
    cM
    @0
    eluzel2
    syl
    @5
    cA
    cz
    @1
    wph
    cA
    cz
    wss
    #
    @4
    wph
    cA
    cZ
    cz
    ssuzfz.2
    cZ
    cz
    wss
    wph
    cZ
    @12
    cz
    ssuzfz.1
    cM
    uzssz
    eqsstri
    a1i
    sstrd
    #
    adantr
    #
    @5
    @15
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    @1
    cA
    wcel
    @17
    @4
    @18
    wph
    cA
    @0
    ne0i
    adantl
    wph
    @19
    @4
    ssuzfz.3
    adantr
    #
    cA
    suprfinzcl
    syl3anc
    sseldd
    wph
    cA
    cz
    @0
    @16
    sselda
    3jca
    @5
    @13
    @10
    @14
    cM
    @0
    eluzle
    syl
    @5
    cA
    @0
    @1
    wph
    cA
    cr
    wss
    @4
    wph
    cA
    cz
    cr
    @16
    cz
    cr
    wss
    wph
    zssre
    a1i
    sstrd
    adantr
    @20
    wph
    @4
    simpr
    @5
    @1
    eqidd
    supfirege
    jca32
    @0
    cM
    @1
    elfz2
    sylibr
    ex
    ralrimiv
    vk
    cA
    @2
    dfss3
    sylibr
end
