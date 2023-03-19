include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cioo.mm"
include "wrex.mm"
include "cc.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprr.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "cxr.mm"
include "readdcld.mm"
include "rexrd.mm"
include "adantr.mm"
include "cr.mm"
include "wss.mm"
include "ioossre.mm"
include "a1i.mm"
include "sselda.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd1dd.mm"
include "iooltub.mm"
include "eliood.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "sylan2b.mm"
include "elioore.mm"
include "adantl.mm"
include "recnd.mm"
include "cmin.mm"
include "resubcld.mm"
include "pncand.mm"
include "eqcomd.mm"
include "ltsub1dd.mm"
include "eqbrtrd.mm"
include "breqtrd.mm"
include "npcand.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem iooshift
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  assume iooshift.1: |- ( ph -> A e. RR )
  assume iooshift.2: |- ( ph -> B e. RR )
  assume iooshift.3: |- ( ph -> T e. RR )

  disjoint A w
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint T w
  disjoint T z
  disjoint ph z
  disjoint A x
  disjoint w x
  disjoint x z
  disjoint B x
  disjoint T x
  disjoint ph x
  assert |- ( ph -> ( ( A + T ) (,) ( B + T ) ) = { w e. CC | E. z e. ( A (,) B ) w = ( z + T ) } )

  proof
    wph
    vw
    cv
    #
    vz
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vz
    cA
    cB
    cioo
    co
    #
    wrex
    #
    vw
    cc
    crab
    #
    cA
    cT
    caddc
    co
    #
    cB
    cT
    caddc
    co
    #
    cioo
    co
    #
    wph
    vx
    @6
    @9
    wph
    vx
    cv
    #
    @6
    wcel
    #
    @10
    @9
    wcel
    #
    @11
    wph
    @10
    cc
    wcel
    #
    @10
    @2
    wceq
    #
    vz
    @4
    wrex
    #
    wa
    #
    @12
    @5
    @15
    vw
    @10
    cc
    @0
    @10
    wceq
    @3
    @14
    vz
    @4
    @0
    @10
    @2
    eqeq1
    rexbidv
    elrab
    #
    wph
    @16
    wa
    #
    @15
    @12
    wph
    @13
    @15
    simprr
    @18
    @14
    @12
    vz
    @4
    wph
    @16
    vz
    wph
    vz
    nfv
    @13
    @15
    vz
    @13
    vz
    nfv
    @14
    vz
    @4
    nfre1
    nfan
    nfan
    @12
    vz
    nfv
    wph
    @1
    @4
    wcel
    #
    @14
    @12
    wi
    wi
    @16
    wph
    @19
    @14
    @12
    wph
    @19
    @14
    w3a
    @10
    @2
    @9
    wph
    @19
    @14
    simp3
    wph
    @19
    @2
    @9
    wcel
    @14
    wph
    @19
    wa
    #
    @7
    @8
    @2
    wph
    @7
    cxr
    wcel
    #
    @19
    wph
    @7
    wph
    cA
    cT
    iooshift.1
    iooshift.3
    readdcld
    #
    rexrd
    #
    adantr
    wph
    @8
    cxr
    wcel
    #
    @19
    wph
    @8
    wph
    cB
    cT
    iooshift.2
    iooshift.3
    readdcld
    #
    rexrd
    #
    adantr
    @20
    @1
    cT
    wph
    @4
    cr
    @1
    @4
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    sselda
    #
    wph
    cT
    cr
    wcel
    #
    @19
    iooshift.3
    adantr
    #
    readdcld
    @20
    cA
    @1
    cT
    wph
    cA
    cr
    wcel
    @19
    iooshift.1
    adantr
    #
    @27
    @29
    @20
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @19
    cA
    @1
    clt
    wbr
    @20
    cA
    @30
    rexrd
    #
    @20
    cB
    wph
    cB
    cr
    wcel
    @19
    iooshift.2
    adantr
    #
    rexrd
    #
    wph
    @19
    simpr
    #
    cA
    cB
    @1
    ioogtlb
    syl3anc
    ltadd1dd
    @20
    @1
    cB
    cT
    @27
    @34
    @29
    @20
    @31
    @32
    @19
    @1
    cB
    clt
    wbr
    @33
    @35
    @36
    cA
    cB
    @1
    iooltub
    syl3anc
    ltadd1dd
    eliood
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    sylan2b
    wph
    @12
    wa
    #
    @13
    @15
    @11
    @37
    @10
    @12
    @10
    cr
    wcel
    wph
    @10
    @7
    @8
    elioore
    adantl
    #
    recnd
    #
    @37
    @10
    cT
    cmin
    co
    #
    @4
    wcel
    @10
    @40
    cT
    caddc
    co
    #
    wceq
    #
    @15
    @37
    cA
    cB
    @40
    wph
    @31
    @12
    wph
    cA
    iooshift.1
    rexrd
    adantr
    wph
    @32
    @12
    wph
    cB
    iooshift.2
    rexrd
    adantr
    @37
    @10
    cT
    @38
    wph
    @28
    @12
    iooshift.3
    adantr
    #
    resubcld
    @37
    cA
    @7
    cT
    cmin
    co
    #
    @40
    clt
    wph
    cA
    @44
    wceq
    @12
    wph
    @44
    cA
    wph
    cA
    cT
    wph
    cA
    iooshift.1
    recnd
    wph
    cT
    iooshift.3
    recnd
    #
    pncand
    eqcomd
    adantr
    @37
    @7
    @10
    cT
    wph
    @7
    cr
    wcel
    @12
    @22
    adantr
    @38
    @43
    @37
    @21
    @24
    @12
    @7
    @10
    clt
    wbr
    wph
    @21
    @12
    @23
    adantr
    #
    wph
    @24
    @12
    @26
    adantr
    #
    wph
    @12
    simpr
    #
    @7
    @8
    @10
    ioogtlb
    syl3anc
    ltsub1dd
    eqbrtrd
    @37
    @40
    @8
    cT
    cmin
    co
    #
    cB
    clt
    @37
    @10
    @8
    cT
    @38
    wph
    @8
    cr
    wcel
    @12
    @25
    adantr
    @43
    @37
    @21
    @24
    @12
    @10
    @8
    clt
    wbr
    @46
    @47
    @48
    @7
    @8
    @10
    iooltub
    syl3anc
    ltsub1dd
    wph
    @49
    cB
    wceq
    @12
    wph
    cB
    cT
    wph
    cB
    iooshift.2
    recnd
    @45
    pncand
    adantr
    breqtrd
    eliood
    @37
    @41
    @10
    @37
    @10
    cT
    @39
    wph
    cT
    cc
    wcel
    @12
    @45
    adantr
    npcand
    eqcomd
    @14
    @42
    vz
    @40
    @4
    @1
    @40
    wceq
    @2
    @41
    @10
    @1
    @40
    cT
    caddc
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @17
    sylanbrc
    impbida
    eqrdv
    eqcomd
end
