include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "creps.mm"
include "cpfx.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "cword.mm"
include "repsw.mm"
include "3adant3.mm"
include "wa.mm"
include "repswlen.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimp3a.mm"
include "pfxlen.mm"
include "syl2anc.mm"
include "elfznn0.mm"
include "anim2i.mm"
include "3adant2.mm"
include "syl.mm"
include "eqtr4d.mm"
include "simpl1.mm"
include "simpl2.mm"
include "cuz.mm"
include "wss.mm"
include "elfzuz3.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "fzoss2.mm"
include "sselda.mm"
include "repswsymb.mm"
include "syl3anc.mm"
include "adantr.mm"
include "biimpa.mm"
include "pfxfv.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "pfxcl.mm"
include "eqwrd.mm"
include "mpbir2and.mm"

theorem repswpfx
  let cS: class S
  let cL: class L
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. V /\ N e. NN0 /\ L e. ( 0 ... N ) ) -> ( ( S repeatS N ) prefix L ) = ( S repeatS L ) )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    cL
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    w3a
    #
    cS
    cN
    creps
    co
    #
    cL
    cpfx
    co
    #
    cS
    cL
    creps
    co
    #
    wceq
    #
    @6
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    wceq
    #
    vi
    cv
    #
    @6
    cfv
    #
    @12
    @7
    cfv
    #
    wceq
    #
    vi
    cc0
    @9
    cfzo
    co
    #
    wral
    #
    @4
    @9
    cL
    @10
    @4
    @5
    cV
    cword
    #
    wcel
    #
    cL
    cc0
    @5
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @9
    cL
    wceq
    @0
    @1
    @19
    @3
    cS
    cN
    cV
    repsw
    3adant3
    #
    @0
    @1
    @3
    @22
    @0
    @1
    wa
    #
    @2
    @21
    cL
    @24
    cN
    @20
    cc0
    cfz
    @24
    @20
    cN
    cS
    cN
    cV
    repswlen
    eqcomd
    oveq2d
    eleq2d
    biimp3a
    #
    cV
    @5
    cL
    pfxlen
    syl2anc
    #
    @4
    @0
    cL
    cn0
    wcel
    #
    wa
    #
    @10
    cL
    wceq
    @0
    @3
    @28
    @1
    @3
    @27
    @0
    cL
    cN
    elfznn0
    #
    anim2i
    3adant2
    #
    cS
    cL
    cV
    repswlen
    syl
    eqtr4d
    @4
    @15
    vi
    @16
    @4
    @12
    @16
    wcel
    #
    wa
    #
    @12
    @5
    cfv
    #
    cS
    @13
    @14
    @32
    @0
    @1
    @12
    cc0
    cN
    cfzo
    co
    #
    wcel
    @33
    cS
    wceq
    @0
    @1
    @3
    @31
    simpl1
    #
    @0
    @1
    @3
    @31
    simpl2
    @4
    @16
    @34
    @12
    @4
    cN
    @9
    cuz
    cfv
    #
    wcel
    @16
    @34
    wss
    @4
    cN
    cL
    cuz
    cfv
    #
    @36
    @3
    @0
    cN
    @37
    wcel
    @1
    cL
    cc0
    cN
    elfzuz3
    3ad2ant3
    @4
    @9
    cL
    cuz
    @26
    fveq2d
    eleqtrrd
    @9
    cc0
    cN
    fzoss2
    syl
    sselda
    cS
    @12
    cN
    cV
    repswsymb
    syl3anc
    @32
    @19
    @22
    @12
    cc0
    cL
    cfzo
    co
    #
    wcel
    #
    @13
    @33
    wceq
    @4
    @19
    @31
    @23
    adantr
    @4
    @22
    @31
    @25
    adantr
    @4
    @31
    @39
    @4
    @16
    @38
    @12
    @4
    @9
    cL
    cc0
    cfzo
    @26
    oveq2d
    eleq2d
    biimpa
    #
    @12
    cL
    cV
    @5
    pfxfv
    syl3anc
    @32
    @0
    @27
    @39
    @14
    cS
    wceq
    @35
    @4
    @27
    @31
    @3
    @0
    @27
    @1
    @29
    3ad2ant3
    adantr
    @40
    cS
    @12
    cL
    cV
    repswsymb
    syl3anc
    3eqtr4d
    ralrimiva
    @4
    @6
    @18
    wcel
    #
    @7
    @18
    wcel
    #
    @8
    @11
    @17
    wa
    wb
    @4
    @19
    @41
    @23
    cV
    @5
    cL
    pfxcl
    syl
    @4
    @28
    @42
    @30
    cS
    cL
    cV
    repsw
    syl
    @6
    vi
    cV
    @7
    eqwrd
    syl2anc
    mpbir2and
end
