include "cc0.mm"
include "wne.mm"
include "wral.mm"
include "cprod.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "1red.mm"
include "nfra1.mm"
include "nfan.mm"
include "cfn.mm"
include "wcel.mm"
include "adantr.mm"
include "cv.mm"
include "cr.mm"
include "adantlr.mm"
include "rspa.mm"
include "adantll.mm"
include "redivcld.mm"
include "fprodreclf.mm"
include "fprodge0.mm"
include "crp.mm"
include "0red.mm"
include "leneltd.mm"
include "elrpd.mm"
include "divge1.mm"
include "syl3anc.mm"
include "fprodge1.mm"
include "lemul2ad.mm"
include "wceq.mm"
include "recnd.mm"
include "fprodclf.mm"
include "mulid1d.mm"
include "cc.mm"
include "fproddivf.mm"
include "oveq2d.mm"
include "fprodn0f.mm"
include "divcan2d.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "breq12d.mm"
include "mpbid.mm"
include "wn.mm"
include "csb.mm"
include "wrex.mm"
include "simpl.mm"
include "nne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfeq.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "cbvrex.mm"
include "3bitr3i.mm"
include "biimpi.mm"
include "adantl.mm"
include "w3a.mm"
include "nf3an.mm"
include "3ad2ant1.mm"
include "3ad2antl1.mm"
include "simp2.mm"
include "biimparc.mm"
include "3ad2antl3.mm"
include "fprodeq0g.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"

theorem fprodle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vj: setvar j
  assume fprodle.kph: |- F/ k ph
  assume fprodle.a: |- ( ph -> A e. Fin )
  assume fprodle.b: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fprodle.0l3b: |- ( ( ph /\ k e. A ) -> 0 <_ B )
  assume fprodle.c: |- ( ( ph /\ k e. A ) -> C e. RR )
  assume fprodle.blec: |- ( ( ph /\ k e. A ) -> B <_ C )

  disjoint A k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint j ph
  assert |- ( ph -> prod_ k e. A B <_ prod_ k e. A C )

  proof
    wph
    cB
    cc0
    wne
    #
    vk
    cA
    wral
    #
    cA
    cB
    vk
    cprod
    #
    cA
    cC
    vk
    cprod
    #
    cle
    wbr
    #
    wph
    @1
    wa
    #
    @2
    c1
    cmul
    co
    #
    @2
    cA
    cC
    cB
    cdiv
    co
    #
    vk
    cprod
    #
    cmul
    co
    #
    cle
    wbr
    @4
    @5
    c1
    @8
    @2
    @5
    1red
    @5
    cA
    @7
    vk
    wph
    @1
    vk
    fprodle.kph
    @0
    vk
    cA
    nfra1
    nfan
    #
    wph
    cA
    cfn
    wcel
    #
    @1
    fprodle.a
    adantr
    #
    @5
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cC
    cB
    wph
    @14
    cC
    cr
    wcel
    #
    @1
    fprodle.c
    adantlr
    #
    wph
    @14
    cB
    cr
    wcel
    @1
    fprodle.b
    adantlr
    #
    @1
    @14
    @0
    wph
    @0
    vk
    cA
    rspa
    adantll
    #
    redivcld
    #
    fprodreclf
    wph
    @2
    cr
    wcel
    @1
    wph
    cA
    cB
    vk
    fprodle.kph
    fprodle.a
    fprodle.b
    fprodreclf
    adantr
    wph
    cc0
    @2
    cle
    wbr
    @1
    wph
    cA
    cB
    vk
    fprodle.kph
    fprodle.a
    fprodle.b
    fprodle.0l3b
    fprodge0
    adantr
    @5
    cA
    @7
    vk
    @10
    @12
    @20
    @15
    cB
    crp
    wcel
    @16
    cB
    cC
    cle
    wbr
    #
    c1
    @7
    cle
    wbr
    @15
    cB
    @18
    @15
    cc0
    cB
    @15
    0red
    @18
    wph
    @14
    cc0
    cB
    cle
    wbr
    @1
    fprodle.0l3b
    adantlr
    @19
    leneltd
    elrpd
    @17
    wph
    @14
    @21
    @1
    fprodle.blec
    adantlr
    cB
    cC
    divge1
    syl3anc
    fprodge1
    lemul2ad
    @5
    @6
    @2
    @9
    @3
    cle
    wph
    @6
    @2
    wceq
    @1
    wph
    @2
    wph
    cA
    cB
    vk
    fprodle.kph
    fprodle.a
    wph
    @14
    wa
    #
    cB
    fprodle.b
    recnd
    #
    fprodclf
    #
    mulid1d
    adantr
    @5
    @9
    @2
    @3
    @2
    cdiv
    co
    #
    cmul
    co
    @3
    @3
    @5
    @8
    @25
    @2
    cmul
    @5
    cA
    cC
    cB
    vk
    @10
    @12
    wph
    @14
    cC
    cc
    wcel
    @1
    @22
    cC
    fprodle.c
    recnd
    #
    adantlr
    wph
    @14
    cB
    cc
    wcel
    #
    @1
    @23
    adantlr
    #
    @19
    fproddivf
    oveq2d
    @5
    @3
    @2
    wph
    @3
    cc
    wcel
    @1
    wph
    cA
    cC
    vk
    fprodle.kph
    fprodle.a
    @26
    fprodclf
    adantr
    wph
    @2
    cc
    wcel
    @1
    @24
    adantr
    @5
    cA
    cB
    vk
    @10
    @12
    @28
    @19
    fprodn0f
    divcan2d
    @5
    @3
    eqidd
    3eqtrd
    breq12d
    mpbid
    wph
    @1
    wn
    #
    wa
    wph
    vk
    vj
    cv
    #
    cB
    csb
    #
    cc0
    wceq
    #
    vj
    cA
    wrex
    #
    @4
    wph
    @29
    simpl
    @29
    @33
    wph
    @29
    @33
    @0
    wn
    #
    vk
    cA
    wrex
    cB
    cc0
    wceq
    #
    vk
    cA
    wrex
    @29
    @33
    @34
    @35
    vk
    cA
    cB
    cc0
    nne
    rexbii
    @0
    vk
    cA
    rexnal
    @35
    @32
    vk
    vj
    cA
    @35
    vj
    nfv
    vk
    @31
    cc0
    vk
    @30
    cB
    nfcsb1v
    vk
    cc0
    nfcv
    nfeq
    #
    @13
    @30
    wceq
    #
    cB
    @31
    cc0
    vk
    @30
    cB
    csbeq1a
    eqeq1d
    #
    cbvrex
    3bitr3i
    biimpi
    adantl
    wph
    @33
    wa
    @2
    cc0
    @3
    cle
    wph
    @33
    @2
    cc0
    wceq
    #
    wph
    @32
    @39
    vj
    cA
    wph
    vj
    nfv
    @39
    vj
    nfv
    wph
    @30
    cA
    wcel
    #
    @32
    @39
    wph
    @40
    @32
    w3a
    cA
    cB
    @30
    vk
    wph
    @40
    @32
    vk
    fprodle.kph
    @40
    vk
    nfv
    @36
    nf3an
    wph
    @40
    @11
    @32
    fprodle.a
    3ad2ant1
    wph
    @40
    @14
    @27
    @32
    @23
    3ad2antl1
    wph
    @40
    @32
    simp2
    @32
    wph
    @37
    @35
    @40
    @37
    @35
    @32
    @38
    biimparc
    3ad2antl3
    fprodeq0g
    3exp
    rexlimd
    imp
    wph
    cc0
    @3
    cle
    wbr
    @33
    wph
    cA
    cC
    vk
    fprodle.kph
    fprodle.a
    fprodle.c
    @22
    cc0
    cB
    cC
    @22
    0red
    fprodle.b
    fprodle.c
    fprodle.0l3b
    fprodle.blec
    letrd
    fprodge0
    adantr
    eqbrtrd
    syl2anc
    pm2.61dan
end
