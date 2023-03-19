include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wral.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "a1i.mm"
include "id.mm"
include "sstrd.mm"
include "adantr.mm"
include "rabn0.mm"
include "bicomi.mm"
include "biimpi.mm"
include "adantl.mm"
include "uzwo.mm"
include "syl2anc.mm"
include "wcel.mm"
include "w3a.mm"
include "wsbc.mm"
include "sseli.mm"
include "3adant1.mm"
include "nfcv.mm"
include "nfsbc1.mm"
include "sbceq1a.mm"
include "elrabf.mm"
include "simprd.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simpl13.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpll.mm"
include "sylibr.mm"
include "adantll.mm"
include "rspa.mm"
include "syl21anc.mm"
include "cr.mm"
include "cz.mm"
include "sselda.mm"
include "eluzelz.mm"
include "syl.mm"
include "zred.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "ssel2.mm"
include "3ad2antl1.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1.mm"
include "ltnled.mm"
include "mpbid.mm"
include "syl3anc.mm"
include "pm2.65da.mm"
include "3exp.mm"
include "ralrimi.mm"
include "jca.mm"
include "nfn.mm"
include "nfim.mm"
include "nfral.mm"
include "nfan.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspce.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem uzwo4
  let wph: wff ph
  let wps: wff ps
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let vi: setvar i
  assume uzwo4.1: |- F/ j ps
  assume uzwo4.2: |- ( j = k -> ( ph <-> ps ) )

  disjoint M k
  disjoint S j
  disjoint S k
  disjoint j k
  disjoint k ph
  disjoint M i
  disjoint i k
  disjoint S i
  disjoint i j
  disjoint i ph
  disjoint i ps
  assert |- ( ( S C_ ( ZZ>= ` M ) /\ E. j e. S ph ) -> E. j e. S ( ph /\ A. k e. S ( k < j -> -. ps ) ) )

  proof
    cS
    cM
    cuz
    cfv
    #
    wss
    #
    wph
    vj
    cS
    wrex
    #
    wa
    #
    vi
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    vk
    wph
    vj
    cS
    crab
    #
    wral
    #
    vi
    @7
    wrex
    #
    wph
    @5
    vj
    cv
    #
    clt
    wbr
    #
    wps
    wn
    #
    wi
    #
    vk
    cS
    wral
    #
    wa
    #
    vj
    cS
    wrex
    #
    @3
    @7
    @0
    wss
    #
    @7
    c0
    wne
    #
    @9
    @1
    @17
    @2
    @1
    @7
    cS
    @0
    @7
    cS
    wss
    @1
    wph
    vj
    cS
    ssrab2
    #
    a1i
    @1
    id
    sstrd
    #
    adantr
    @2
    @18
    @1
    @2
    @18
    @18
    @2
    wph
    vj
    cS
    rabn0
    bicomi
    biimpi
    adantl
    @7
    vi
    vk
    cM
    uzwo
    syl2anc
    @1
    @9
    @16
    wi
    @2
    @1
    @8
    @16
    vi
    @7
    @1
    @4
    @7
    wcel
    #
    @8
    @16
    @1
    @21
    @8
    w3a
    #
    @4
    cS
    wcel
    #
    wph
    vj
    @4
    wsbc
    #
    @5
    @4
    clt
    wbr
    #
    @12
    wi
    #
    vk
    cS
    wral
    #
    wa
    #
    @16
    @21
    @8
    @23
    @1
    @21
    @23
    @8
    @7
    cS
    @4
    @19
    sseli
    adantr
    3adant1
    @22
    @24
    @27
    @21
    @8
    @24
    @1
    @21
    @24
    @8
    @21
    @23
    @24
    @21
    @23
    @24
    wa
    wph
    @24
    vj
    @4
    cS
    vj
    @4
    nfcv
    #
    vj
    cS
    nfcv
    #
    wph
    vj
    @4
    @29
    nfsbc1
    #
    wph
    vj
    @4
    sbceq1a
    #
    elrabf
    biimpi
    simprd
    adantr
    3adant1
    @22
    @26
    vk
    cS
    @1
    @21
    @8
    vk
    @1
    vk
    nfv
    @21
    vk
    nfv
    @6
    vk
    @7
    nfra1
    nf3an
    @22
    @5
    cS
    wcel
    #
    @25
    @12
    @22
    @33
    @25
    w3a
    #
    wps
    @6
    @34
    wps
    wa
    @8
    @33
    wps
    @6
    @1
    @21
    @8
    @33
    @25
    wps
    simpl13
    @22
    @33
    @25
    wps
    simpl2
    @34
    wps
    simpr
    @8
    @33
    wa
    wps
    wa
    @8
    @5
    @7
    wcel
    #
    @6
    @8
    @33
    wps
    simpll
    @33
    wps
    @35
    @8
    @33
    wps
    wa
    #
    @36
    @35
    @36
    id
    wph
    wps
    vj
    @5
    cS
    vj
    @5
    nfcv
    @30
    uzwo4.1
    uzwo4.2
    elrabf
    sylibr
    adantll
    @6
    vk
    @7
    rspa
    syl2anc
    syl21anc
    @34
    @6
    wn
    #
    wps
    @34
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @25
    @37
    @22
    @33
    @38
    @25
    @1
    @21
    @38
    @8
    @1
    @21
    wa
    #
    @4
    @40
    @4
    @0
    wcel
    @4
    cz
    wcel
    @1
    @7
    @0
    @4
    @20
    sselda
    cM
    @4
    eluzelz
    syl
    zred
    3adant3
    3ad2ant1
    @22
    @33
    @39
    @25
    @1
    @21
    @33
    @39
    @8
    @1
    @33
    wa
    #
    @5
    @41
    @5
    @0
    wcel
    @5
    cz
    wcel
    cS
    @0
    @5
    ssel2
    cM
    @5
    eluzelz
    syl
    zred
    3ad2antl1
    3adant3
    @22
    @33
    @25
    simp3
    @38
    @39
    @25
    w3a
    #
    @25
    @37
    @38
    @39
    @25
    simp3
    @42
    @5
    @4
    @38
    @39
    @25
    simp2
    @38
    @39
    @25
    simp1
    ltnled
    mpbid
    syl3anc
    adantr
    pm2.65da
    3exp
    ralrimi
    jca
    @15
    @28
    vj
    @4
    cS
    @24
    @27
    vj
    @31
    @26
    vj
    vk
    cS
    @30
    @25
    @12
    vj
    @25
    vj
    nfv
    wps
    vj
    uzwo4.1
    nfn
    nfim
    nfral
    nfan
    @10
    @4
    wceq
    #
    wph
    @24
    @14
    @27
    @32
    @43
    @13
    @26
    vk
    cS
    @43
    @11
    @25
    @12
    @10
    @4
    @5
    clt
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspce
    syl2anc
    3exp
    rexlimdv
    adantr
    mpd
end
