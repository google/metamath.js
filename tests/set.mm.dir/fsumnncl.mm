include "csu.mm"
include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "cv.mm"
include "nnnn0d.mm"
include "fsumnn0cl.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "csn.mm"
include "cdif.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "0red.mm"
include "wi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nnred.mm"
include "readdcld.mm"
include "cr.mm"
include "cfn.mm"
include "diffi.mm"
include "syl.mm"
include "eldifi.mm"
include "adantl.mm"
include "syldan.mm"
include "nn0red.mm"
include "adantr.mm"
include "nnrpd.mm"
include "ltaddrpd.mm"
include "cle.mm"
include "nn0ge0d.mm"
include "leadd1dd.mm"
include "ltletrd.mm"
include "cun.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "sumeq1d.mm"
include "simpr.mm"
include "neldifsnd.mm"
include "cc.mm"
include "simpl.mm"
include "syl2anc.mm"
include "nncnd.mm"
include "adantlr.mm"
include "wss.mm"
include "nnsscn.mm"
include "a1i.mm"
include "sseldd.mm"
include "fsumsplitsn.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "jca.mm"
include "elnnnn0b.mm"
include "sylibr.mm"

theorem fsumnncl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vj: setvar j
  assume fsumnncl.an0: |- ( ph -> A =/= (/) )
  assume fsumnncl.afi: |- ( ph -> A e. Fin )
  assume fsumnncl.b: |- ( ( ph /\ k e. A ) -> B e. NN )

  disjoint A k
  disjoint k ph
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint j ph
  assert |- ( ph -> sum_ k e. A B e. NN )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cn0
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    wa
    @0
    cn
    wcel
    wph
    @1
    @2
    wph
    cA
    cB
    vk
    fsumnncl.afi
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    fsumnncl.b
    nnnn0d
    #
    fsumnn0cl
    wph
    vj
    cv
    #
    cA
    wcel
    #
    vj
    wex
    #
    @2
    wph
    cA
    c0
    wne
    @9
    fsumnncl.an0
    vj
    cA
    n0
    sylib
    wph
    @8
    @2
    vj
    wph
    @8
    @2
    wph
    @8
    wa
    #
    cc0
    cA
    @7
    csn
    #
    cdif
    #
    cB
    vk
    csu
    #
    vk
    @7
    cB
    csb
    #
    caddc
    co
    #
    @0
    clt
    @10
    cc0
    cc0
    @14
    caddc
    co
    @15
    @10
    0red
    #
    @10
    cc0
    @14
    @16
    @10
    @14
    @5
    cB
    cn
    wcel
    #
    wi
    @10
    @14
    cn
    wcel
    #
    wi
    vk
    vj
    @10
    @18
    vk
    @10
    vk
    nfv
    #
    vk
    @14
    cn
    vk
    @7
    cB
    nfcsb1v
    #
    nfel1
    nfim
    @3
    @7
    wceq
    #
    @5
    @10
    @17
    @18
    @21
    @4
    @8
    wph
    @3
    @7
    cA
    eleq1
    anbi2d
    @21
    cB
    @14
    cn
    vk
    @7
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    fsumnncl.b
    chvar
    #
    nnred
    #
    readdcld
    @10
    @13
    @14
    wph
    @13
    cr
    wcel
    @8
    wph
    @13
    wph
    @12
    cB
    vk
    wph
    cA
    cfn
    wcel
    @12
    cfn
    wcel
    #
    fsumnncl.afi
    cA
    @11
    diffi
    syl
    #
    wph
    @3
    @12
    wcel
    #
    @4
    cB
    cn0
    wcel
    @27
    @4
    wph
    @3
    cA
    @11
    eldifi
    adantl
    #
    @6
    syldan
    fsumnn0cl
    #
    nn0red
    adantr
    #
    @24
    readdcld
    @10
    cc0
    @14
    @16
    @10
    @14
    @23
    nnrpd
    ltaddrpd
    @10
    cc0
    @13
    @14
    @16
    @30
    @24
    wph
    cc0
    @13
    cle
    wbr
    @8
    wph
    @13
    @29
    nn0ge0d
    adantr
    leadd1dd
    ltletrd
    @10
    @0
    @12
    @11
    cun
    #
    cB
    vk
    csu
    @15
    @10
    cA
    @31
    cB
    vk
    @10
    @31
    cA
    @8
    @31
    cA
    wceq
    wph
    cA
    @7
    difsnid
    adantl
    eqcomd
    sumeq1d
    @10
    @12
    @7
    cB
    @14
    vk
    cA
    @19
    @20
    wph
    @25
    @8
    @26
    adantr
    wph
    @8
    simpr
    @10
    @7
    cA
    neldifsnd
    wph
    @27
    cB
    cc
    wcel
    @8
    wph
    @27
    wa
    #
    cB
    @32
    wph
    @4
    @17
    wph
    @27
    simpl
    @28
    fsumnncl.b
    syl2anc
    nncnd
    adantlr
    @22
    @10
    cn
    cc
    @14
    cn
    cc
    wss
    @10
    nnsscn
    a1i
    @23
    sseldd
    fsumsplitsn
    eqtr2d
    breqtrd
    ex
    exlimdv
    mpd
    jca
    @0
    elnnnn0b
    sylibr
end
