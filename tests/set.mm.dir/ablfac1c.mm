include "cfn.mm"
include "wcel.mm"
include "cdprd.mm"
include "co.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "dprdssv.mm"
include "a1i.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cdvds.mm"
include "ssfi.mm"
include "sylancl.mm"
include "hashcl.mm"
include "syl.mm"
include "csubg.mm"
include "cdm.mm"
include "ablfac1b.mm"
include "dprdsubg.mm"
include "lagsubg.mm"
include "syl2anc.mm"
include "cv.mm"
include "cpc.mm"
include "cle.mm"
include "cprime.mm"
include "wral.mm"
include "wa.mm"
include "breq1.mm"
include "elrab2.mm"
include "sseld.mm"
include "syl5bir.mm"
include "impl.mm"
include "cexp.mm"
include "ablfac1a.mm"
include "cress.mm"
include "cbs.mm"
include "crab.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "dmmpti.mm"
include "dprdf2.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "simpr.mm"
include "dprdub.mm"
include "wb.mm"
include "eqid.mm"
include "subsubg.mm"
include "mpbir2and.mm"
include "subgbas.mm"
include "eqeltrrd.mm"
include "fveq2d.mm"
include "breqtrrd.mm"
include "eqbrtrrd.mm"
include "cz.mm"
include "sselda.mm"
include "nn0zd.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "cabl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "grpbn0.mm"
include "3syl.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "syldan.mm"
include "pcdvdsb.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "wn.mm"
include "cc0.mm"
include "pceq0.mm"
include "biimpar.mm"
include "c0g.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "nn0ge0d.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "pc2dvds.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "hashen.mm"
include "mpbid.mm"
include "fisseneq.mm"

theorem ablfac1c
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cG: class G
  let cO: class O
  let vp: setvar p
  let vq: setvar q
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let cP: class P
  let cT: class T
  assume ablfac1.b: |- B = ( Base ` G )
  assume ablfac1.o: |- O = ( od ` G )
  assume ablfac1.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac1.g: |- ( ph -> G e. Abel )
  assume ablfac1.f: |- ( ph -> B e. Fin )
  assume ablfac1.1: |- ( ph -> A C_ Prime )
  assume ablfac1c.d: |- D = { w e. Prime | w || ( # ` B ) }
  assume ablfac1.2: |- ( ph -> D C_ A )

  disjoint p w
  disjoint p x
  disjoint B p
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint D p
  disjoint D x
  disjoint p ph
  disjoint ph w
  disjoint ph x
  disjoint A p
  disjoint A x
  disjoint O p
  disjoint O x
  disjoint G p
  disjoint G x
  disjoint p q
  disjoint p y
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint B q
  disjoint w y
  disjoint x y
  disjoint B y
  disjoint D q
  disjoint D y
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p z
  disjoint q z
  disjoint ph q
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S b
  disjoint S q
  disjoint A a
  disjoint A b
  disjoint A q
  disjoint A y
  disjoint A z
  disjoint O q
  disjoint O y
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint T q
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint G a
  disjoint G b
  disjoint G q
  disjoint G y
  disjoint G z
  assert |- ( ph -> ( G DProd S ) = B )

  proof
    wph
    cB
    cfn
    wcel
    #
    cG
    cS
    cdprd
    co
    #
    cB
    wss
    #
    @1
    cB
    cen
    wbr
    #
    @1
    cB
    wceq
    ablfac1.f
    @2
    wph
    cB
    cS
    cG
    ablfac1.b
    dprdssv
    #
    a1i
    wph
    @1
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    wceq
    #
    @3
    wph
    @5
    cn0
    wcel
    #
    @6
    cn0
    wcel
    #
    @5
    @6
    cdvds
    wbr
    #
    @6
    @5
    cdvds
    wbr
    #
    @7
    wph
    @1
    cfn
    wcel
    #
    @8
    wph
    @0
    @2
    @12
    ablfac1.f
    @4
    cB
    @1
    ssfi
    sylancl
    #
    @1
    hashcl
    syl
    #
    wph
    @0
    @9
    ablfac1.f
    cB
    hashcl
    syl
    #
    wph
    @1
    cG
    csubg
    cfv
    #
    wcel
    #
    @0
    @10
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    @17
    wph
    vx
    cA
    cB
    cS
    cG
    cO
    vp
    ablfac1.b
    ablfac1.o
    ablfac1.s
    ablfac1.g
    ablfac1.f
    ablfac1.1
    ablfac1b
    #
    cS
    cG
    dprdsubg
    syl
    #
    ablfac1.f
    cG
    cB
    @1
    ablfac1.b
    lagsubg
    syl2anc
    wph
    @11
    vq
    cv
    #
    @6
    cpc
    co
    #
    @21
    @5
    cpc
    co
    #
    cle
    wbr
    #
    vq
    cprime
    wral
    #
    wph
    @24
    vq
    cprime
    wph
    @21
    cprime
    wcel
    #
    wa
    #
    @21
    @6
    cdvds
    wbr
    #
    @24
    @27
    @28
    @21
    cA
    wcel
    #
    @24
    wph
    @26
    @28
    @29
    @26
    @28
    wa
    @21
    cD
    wcel
    wph
    @29
    vw
    cv
    #
    @6
    cdvds
    wbr
    @28
    vw
    @21
    cprime
    cD
    @30
    @21
    @6
    cdvds
    breq1
    ablfac1c.d
    elrab2
    wph
    cD
    cA
    @21
    ablfac1.2
    sseld
    syl5bir
    impl
    wph
    @29
    @24
    @26
    wph
    @29
    wa
    #
    @24
    @21
    @22
    cexp
    co
    #
    @5
    cdvds
    wbr
    #
    @31
    @21
    cS
    cfv
    #
    chash
    cfv
    #
    @32
    @5
    cdvds
    wph
    vx
    cA
    cB
    @21
    cS
    cG
    cO
    vp
    ablfac1.b
    ablfac1.o
    ablfac1.s
    ablfac1.g
    ablfac1.f
    ablfac1.1
    ablfac1a
    @31
    @35
    cG
    @1
    cress
    co
    #
    cbs
    cfv
    #
    chash
    cfv
    #
    @5
    cdvds
    @31
    @34
    @36
    csubg
    cfv
    wcel
    #
    @37
    cfn
    wcel
    @35
    @38
    cdvds
    wbr
    @31
    @39
    @34
    @16
    wcel
    #
    @34
    @1
    wss
    #
    wph
    cA
    @16
    @21
    cS
    wph
    cS
    cG
    cA
    @19
    cS
    cdm
    cA
    wceq
    #
    wph
    vp
    cA
    vx
    cv
    cO
    cfv
    vp
    cv
    #
    @43
    @6
    cpc
    co
    cexp
    co
    cdvds
    wbr
    #
    vx
    cB
    crab
    cS
    @44
    vx
    cB
    cB
    cG
    cbs
    cfv
    cvv
    ablfac1.b
    cG
    cbs
    fvex
    eqeltri
    rabex
    ablfac1.s
    dmmpti
    #
    a1i
    dprdf2
    ffvelrnda
    @31
    cS
    cG
    cA
    @21
    wph
    @18
    @29
    @19
    adantr
    @42
    @31
    @45
    a1i
    wph
    @29
    simpr
    dprdub
    @31
    @17
    @39
    @40
    @41
    wa
    wb
    wph
    @17
    @29
    @20
    adantr
    #
    @34
    @1
    cG
    @36
    @36
    eqid
    #
    subsubg
    syl
    mpbir2and
    @31
    @1
    @37
    cfn
    @31
    @17
    @1
    @37
    wceq
    @46
    @1
    cG
    @36
    @47
    subgbas
    syl
    #
    wph
    @12
    @29
    @13
    adantr
    eqeltrrd
    @36
    @37
    @34
    @37
    eqid
    lagsubg
    syl2anc
    @31
    @1
    @37
    chash
    @48
    fveq2d
    breqtrrd
    eqbrtrrd
    @31
    @26
    @5
    cz
    wcel
    #
    @22
    cn0
    wcel
    #
    @24
    @33
    wb
    wph
    cA
    cprime
    @21
    ablfac1.1
    sselda
    #
    wph
    @49
    @29
    wph
    @5
    @14
    nn0zd
    #
    adantr
    wph
    @29
    @26
    @50
    @51
    @27
    @21
    @6
    wph
    @26
    simpr
    #
    wph
    @6
    cn
    wcel
    #
    @26
    wph
    @54
    cB
    c0
    wne
    #
    wph
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    @55
    ablfac1.g
    cG
    ablgrp
    cB
    cG
    ablfac1.b
    grpbn0
    3syl
    wph
    @0
    @54
    @55
    wb
    ablfac1.f
    cB
    hashnncl
    syl
    mpbird
    adantr
    #
    pccld
    syldan
    @22
    @21
    @5
    pcdvdsb
    syl3anc
    mpbird
    adantlr
    syldan
    @27
    @28
    wn
    #
    wa
    @22
    cc0
    @23
    cle
    @27
    @22
    cc0
    wceq
    #
    @57
    @27
    @26
    @54
    @58
    @57
    wb
    @53
    @56
    @21
    @6
    pceq0
    syl2anc
    biimpar
    @27
    cc0
    @23
    cle
    wbr
    @57
    @27
    @23
    @27
    @21
    @5
    @53
    wph
    @5
    cn
    wcel
    #
    @26
    wph
    @59
    @1
    c0
    wne
    #
    wph
    @17
    cG
    c0g
    cfv
    #
    @1
    wcel
    @60
    @20
    @1
    cG
    @61
    @61
    eqid
    subg0cl
    @1
    @61
    ne0i
    3syl
    wph
    @12
    @59
    @60
    wb
    @13
    @1
    hashnncl
    syl
    mpbird
    adantr
    pccld
    nn0ge0d
    adantr
    eqbrtrd
    pm2.61dan
    ralrimiva
    wph
    @6
    cz
    wcel
    @49
    @11
    @25
    wb
    wph
    @6
    @15
    nn0zd
    @52
    @6
    @5
    vq
    pc2dvds
    syl2anc
    mpbird
    @5
    @6
    dvdseq
    syl22anc
    wph
    @12
    @0
    @7
    @3
    wb
    @13
    ablfac1.f
    @1
    cB
    hashen
    syl2anc
    mpbid
    @1
    cB
    fisseneq
    syl3anc
end
