include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "ccnv.mm"
include "cc.mm"
include "cdif.mm"
include "csup.mm"
include "cv.mm"
include "wral.mm"
include "simp2.mm"
include "wa.mm"
include "wne.mm"
include "cun.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "cz.mm"
include "wrex.mm"
include "dgrlem.mm"
include "simpld.mm"
include "3ad2ant1.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "biimpa.mm"
include "simprd.mm"
include "eldifsni.mm"
include "syl.mm"
include "wi.mm"
include "simp3.mm"
include "coef3.mm"
include "plyco0.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "mpd.mm"
include "nn0red.mm"
include "cr.mm"
include "adantr.mm"
include "lenltd.mm"
include "ralrimiva.mm"
include "wor.mm"
include "wss.mm"
include "nn0ssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "0zd.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "nn0uz.mm"
include "uzsupss.mm"
include "syl3anc.mm"
include "supnub.mm"
include "mp2and.mm"
include "cdgr.mm"
include "dgrval.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "mtbird.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "mpbird.mm"

theorem dgrlb
  let cA: class A
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let vm: setvar m
  let cB: class B
  let cX: class X
  assume dgrub.1: |- A = ( coeff ` F )
  assume dgrub.2: |- N = ( deg ` F )


  assert |- ( ( F e. ( Poly ` S ) /\ M e. NN0 /\ ( A " ( ZZ>= ` ( M + 1 ) ) ) = { 0 } ) -> N <_ M )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cM
    cn0
    wcel
    #
    cA
    cM
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    #
    wceq
    #
    w3a
    #
    cN
    cM
    cle
    wbr
    cM
    cN
    clt
    wbr
    #
    wn
    @4
    @5
    cM
    cA
    ccnv
    cc
    @2
    cdif
    #
    cima
    #
    cn0
    clt
    csup
    #
    clt
    wbr
    #
    @4
    @1
    cM
    vy
    cv
    #
    clt
    wbr
    wn
    #
    vy
    @7
    wral
    @9
    wn
    @0
    @1
    @3
    simp2
    #
    @4
    @11
    vy
    @7
    @4
    @10
    @7
    wcel
    #
    wa
    #
    @10
    cM
    cle
    wbr
    #
    @11
    @14
    @10
    cA
    cfv
    #
    cc0
    wne
    #
    @15
    @14
    @16
    @6
    wcel
    #
    @17
    @14
    @10
    cn0
    wcel
    #
    @18
    @4
    @13
    @19
    @18
    wa
    #
    @4
    cn0
    cS
    @2
    cun
    #
    cA
    wf
    #
    cA
    cn0
    wfn
    @13
    @20
    wb
    @0
    @1
    @22
    @3
    @0
    @22
    vx
    cv
    #
    vn
    cv
    #
    cle
    wbr
    vx
    @7
    wral
    vn
    cz
    wrex
    #
    vx
    cA
    cS
    vn
    cF
    dgrub.1
    dgrlem
    #
    simpld
    #
    3ad2ant1
    cn0
    @21
    cA
    ffn
    cn0
    @10
    @6
    cA
    elpreima
    3syl
    biimpa
    #
    simprd
    @16
    cc
    cc0
    eldifsni
    syl
    @4
    @13
    @19
    @17
    @15
    wi
    #
    @14
    @19
    @18
    @28
    simpld
    #
    @4
    @29
    vy
    cn0
    @4
    @3
    @29
    vy
    cn0
    wral
    #
    @0
    @1
    @3
    simp3
    @4
    @1
    cn0
    cc
    cA
    wf
    #
    @3
    @31
    wb
    @12
    @0
    @1
    @32
    @3
    cA
    cS
    cF
    dgrub.1
    coef3
    3ad2ant1
    cA
    vy
    cM
    plyco0
    syl2anc
    mpbid
    r19.21bi
    syldan
    mpd
    @14
    @10
    cM
    @14
    @10
    @30
    nn0red
    @4
    cM
    cr
    wcel
    @13
    @4
    cM
    @12
    nn0red
    #
    adantr
    lenltd
    mpbid
    ralrimiva
    @4
    vn
    vx
    vy
    cn0
    @7
    cM
    clt
    cn0
    clt
    wor
    #
    @4
    cn0
    cr
    wss
    cr
    clt
    wor
    @34
    nn0ssre
    ltso
    cn0
    cr
    clt
    soss
    mp2
    a1i
    @0
    @1
    @24
    @23
    clt
    wbr
    wn
    vx
    @7
    wral
    @23
    @24
    clt
    wbr
    @23
    @10
    clt
    wbr
    vy
    @7
    wrex
    wi
    vx
    cn0
    wral
    wa
    vn
    cn0
    wrex
    #
    @3
    @0
    cc0
    cz
    wcel
    @7
    cn0
    wss
    @25
    @35
    @0
    0zd
    @0
    cA
    cdm
    #
    @7
    cn0
    cA
    @6
    cnvimass
    @0
    @22
    @36
    cn0
    wceq
    @27
    cn0
    @21
    cA
    fdm
    syl
    syl5sseq
    @0
    @22
    @25
    @26
    simprd
    vn
    vx
    vy
    @7
    cc0
    cn0
    nn0uz
    uzsupss
    syl3anc
    3ad2ant1
    supnub
    mp2and
    @4
    cN
    @8
    cM
    clt
    @0
    @1
    cN
    @8
    wceq
    @3
    @0
    cN
    cF
    cdgr
    cfv
    #
    @8
    dgrub.2
    cA
    cS
    cF
    dgrub.1
    dgrval
    syl5eq
    3ad2ant1
    breq2d
    mtbird
    @4
    cN
    cM
    @4
    cN
    @0
    @1
    cN
    cn0
    wcel
    @3
    @0
    cN
    @37
    cn0
    dgrub.2
    cS
    cF
    dgrcl
    syl5eqel
    3ad2ant1
    nn0red
    @33
    lenltd
    mpbird
end
