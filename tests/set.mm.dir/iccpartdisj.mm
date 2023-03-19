include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cico.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "wrmo.mm"
include "wal.mm"
include "wdisj.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "nfv.mm"
include "nfreu1.mm"
include "wa.mm"
include "simpl.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "cn.mm"
include "adantr.mm"
include "ciccp.mm"
include "cfz.mm"
include "cn0.mm"
include "nnnn0.mm"
include "0elfz.mm"
include "3syl.mm"
include "iccpartxr.mm"
include "nn0fz0.mm"
include "biimpi.mm"
include "wral.mm"
include "iccpartgel.mm"
include "elfzofz.mm"
include "adantl.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspcv.mm"
include "syl.mm"
include "ex.mm"
include "mpid.mm"
include "imp.mm"
include "iccpartleu.mm"
include "fzofzp1.mm"
include "breq1d.mm"
include "icossico.mm"
include "syl22anc.mm"
include "sseld.mm"
include "icceuelpart.mm"
include "syl6an.mm"
include "rexlimd.mm"
include "rmo5.mm"
include "sylibr.mm"
include "alrimiv.mm"
include "df-disj.mm"

theorem iccpartdisj
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vp: setvar p
  let cX: class X
  let vx: setvar x
  let cI: class I
  let cJ: class J
  assume iccpartiun.m: |- ( ph -> M e. NN )
  assume iccpartiun.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M i
  disjoint P i
  disjoint i ph
  disjoint M j
  disjoint M k
  disjoint M p
  disjoint i j
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint k p
  disjoint P j
  disjoint P k
  disjoint P p
  disjoint X i
  disjoint X p
  disjoint M x
  disjoint i x
  disjoint p x
  disjoint P x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint I i
  disjoint I j
  disjoint J j
  disjoint X j
  disjoint p ph
  disjoint k x
  assert |- ( ph -> Disj_ i e. ( 0 ..^ M ) ( ( P ` i ) [,) ( P ` ( i + 1 ) ) ) )

  proof
    wph
    vp
    cv
    #
    vi
    cv
    #
    cP
    cfv
    #
    @1
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cico
    co
    #
    wcel
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wrmo
    #
    vp
    wal
    vi
    @7
    @5
    wdisj
    wph
    @8
    vp
    wph
    @6
    vi
    @7
    wrex
    @6
    vi
    @7
    wreu
    #
    wi
    @8
    wph
    @6
    @9
    vi
    @7
    wph
    vi
    nfv
    @6
    vi
    @7
    nfreu1
    wph
    @1
    @7
    wcel
    #
    @6
    @9
    wi
    wph
    @10
    wa
    #
    wph
    @6
    @0
    cc0
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    cico
    co
    #
    wcel
    @9
    wph
    @10
    simpl
    @11
    @5
    @14
    @0
    @11
    @12
    cxr
    wcel
    @13
    cxr
    wcel
    @12
    @2
    cle
    wbr
    #
    @4
    @13
    cle
    wbr
    #
    @5
    @14
    wss
    @11
    cP
    cc0
    cM
    wph
    cM
    cn
    wcel
    #
    @10
    iccpartiun.m
    adantr
    #
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    @10
    iccpartiun.p
    adantr
    #
    wph
    cc0
    cc0
    cM
    cfz
    co
    #
    wcel
    #
    @10
    wph
    @17
    cM
    cn0
    wcel
    #
    @21
    iccpartiun.m
    cM
    nnnn0
    #
    cM
    0elfz
    3syl
    adantr
    iccpartxr
    @11
    cP
    cM
    cM
    @18
    @19
    wph
    cM
    @20
    wcel
    #
    @10
    wph
    @17
    @22
    @24
    iccpartiun.m
    @23
    @22
    @24
    cM
    nn0fz0
    biimpi
    3syl
    adantr
    iccpartxr
    wph
    @10
    @15
    wph
    @10
    @12
    vj
    cv
    #
    cP
    cfv
    #
    cle
    wbr
    #
    vj
    @20
    wral
    #
    @15
    wph
    cP
    vj
    cM
    iccpartiun.m
    iccpartiun.p
    iccpartgel
    wph
    @10
    @28
    @15
    wi
    #
    @11
    @1
    @20
    wcel
    #
    @29
    @10
    @30
    wph
    @1
    cc0
    cM
    elfzofz
    adantl
    @27
    @15
    vj
    @1
    @20
    @25
    @1
    wceq
    @26
    @2
    @12
    cle
    @25
    @1
    cP
    fveq2
    breq2d
    rspcv
    syl
    ex
    mpid
    imp
    wph
    @10
    @16
    wph
    @10
    @26
    @13
    cle
    wbr
    #
    vj
    @20
    wral
    #
    @16
    wph
    cP
    vj
    cM
    iccpartiun.m
    iccpartiun.p
    iccpartleu
    wph
    @10
    @32
    @16
    wi
    #
    @11
    @3
    @20
    wcel
    #
    @33
    @10
    @34
    wph
    cc0
    cM
    @1
    fzofzp1
    adantl
    @31
    @16
    vj
    @3
    @20
    @25
    @3
    wceq
    @26
    @4
    @13
    cle
    @25
    @3
    cP
    fveq2
    breq1d
    rspcv
    syl
    ex
    mpid
    imp
    @12
    @13
    @2
    @4
    icossico
    syl22anc
    sseld
    wph
    cP
    vi
    cM
    @0
    iccpartiun.m
    iccpartiun.p
    icceuelpart
    syl6an
    ex
    rexlimd
    @6
    vi
    @7
    rmo5
    sylibr
    alrimiv
    vi
    vp
    @7
    @5
    df-disj
    sylibr
end
