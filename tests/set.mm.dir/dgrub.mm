include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "ccnv.mm"
include "cc.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "csup.mm"
include "simp1.mm"
include "simp2.mm"
include "wf.mm"
include "coef3.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cun.mm"
include "wfn.mm"
include "wa.mm"
include "wb.mm"
include "coef.mm"
include "ffn.mm"
include "elpreima.mm"
include "4syl.mm"
include "mpbir2and.mm"
include "wor.mm"
include "cr.mm"
include "wss.mm"
include "nn0ssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "cz.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "0zd.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "dgrlem.mm"
include "simprd.mm"
include "nn0uz.mm"
include "uzsupss.mm"
include "syl3anc.mm"
include "supub.mm"
include "sylc.mm"
include "cdgr.mm"
include "dgrval.mm"
include "syl5eq.mm"
include "breq1d.mm"
include "mtbird.mm"
include "nn0red.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "lenltd.mm"
include "mpbird.mm"

theorem dgrub
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


  assert |- ( ( F e. ( Poly ` S ) /\ M e. NN0 /\ ( A ` M ) =/= 0 ) -> M <_ N )

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
    cM
    cA
    cfv
    #
    cc0
    wne
    #
    w3a
    #
    cM
    cN
    cle
    wbr
    cN
    cM
    clt
    wbr
    #
    wn
    @4
    @5
    cA
    ccnv
    cc
    cc0
    csn
    #
    cdif
    #
    cima
    #
    cn0
    clt
    csup
    #
    cM
    clt
    wbr
    #
    @4
    @0
    cM
    @8
    wcel
    #
    @10
    wn
    @0
    @1
    @3
    simp1
    #
    @4
    @11
    @1
    @2
    @7
    wcel
    #
    @0
    @1
    @3
    simp2
    #
    @4
    @2
    cc
    wcel
    @3
    @13
    @4
    cn0
    cc
    cM
    cA
    @4
    @0
    cn0
    cc
    cA
    wf
    @12
    cA
    cS
    cF
    dgrub.1
    coef3
    syl
    @14
    ffvelrnd
    @0
    @1
    @3
    simp3
    @2
    cc
    cc0
    eldifsn
    sylanbrc
    @4
    @0
    cn0
    cS
    @6
    cun
    #
    cA
    wf
    #
    cA
    cn0
    wfn
    @11
    @1
    @13
    wa
    wb
    @12
    cA
    cS
    cF
    dgrub.1
    coef
    #
    cn0
    @15
    cA
    ffn
    cn0
    cM
    @7
    cA
    elpreima
    4syl
    mpbir2and
    @0
    vn
    vx
    vy
    cn0
    @8
    cM
    clt
    cn0
    clt
    wor
    #
    @0
    cn0
    cr
    wss
    cr
    clt
    wor
    @18
    nn0ssre
    ltso
    cn0
    cr
    clt
    soss
    mp2
    a1i
    @0
    cc0
    cz
    wcel
    @8
    cn0
    wss
    vx
    cv
    #
    vn
    cv
    #
    cle
    wbr
    vx
    @8
    wral
    vn
    cz
    wrex
    #
    @20
    @19
    clt
    wbr
    wn
    vx
    @8
    wral
    @19
    @20
    clt
    wbr
    @19
    vy
    cv
    clt
    wbr
    vy
    @8
    wrex
    wi
    vx
    cn0
    wral
    wa
    vn
    cn0
    wrex
    @0
    0zd
    @0
    cA
    cdm
    #
    @8
    cn0
    cA
    @7
    cnvimass
    @0
    @16
    @22
    cn0
    wceq
    @17
    cn0
    @15
    cA
    fdm
    syl
    syl5sseq
    @0
    @16
    @21
    vx
    cA
    cS
    vn
    cF
    dgrub.1
    dgrlem
    simprd
    vn
    vx
    vy
    @8
    cc0
    cn0
    nn0uz
    uzsupss
    syl3anc
    supub
    sylc
    @4
    cN
    @9
    cM
    clt
    @4
    @0
    cN
    @9
    wceq
    @12
    @0
    cN
    cF
    cdgr
    cfv
    #
    @9
    dgrub.2
    cA
    cS
    cF
    dgrub.1
    dgrval
    syl5eq
    syl
    breq1d
    mtbird
    @4
    cM
    cN
    @4
    cM
    @14
    nn0red
    @4
    cN
    @4
    @0
    cN
    cn0
    wcel
    @12
    @0
    cN
    @23
    cn0
    dgrub.2
    cS
    cF
    dgrcl
    syl5eqel
    syl
    nn0red
    lenltd
    mpbird
end
