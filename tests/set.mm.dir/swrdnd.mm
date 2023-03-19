include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "chash.mm"
include "cfv.mm"
include "w3o.mm"
include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "3orcomb.mm"
include "df-3or.mm"
include "bitri.mm"
include "swrdlend.mm"
include "com12.mm"
include "wn.mm"
include "wa.mm"
include "cfzo.mm"
include "cdm.mm"
include "wss.mm"
include "cmin.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cif.mm"
include "swrdval.mm"
include "adantl.mm"
include "wb.mm"
include "zre.mm"
include "0red.mm"
include "ltnled.mm"
include "3ad2ant2.mm"
include "cr.mm"
include "lencl.mm"
include "nn0red.mm"
include "anim12i.mm"
include "3adant2.mm"
include "ltnle.mm"
include "syl.mm"
include "orbi12d.mm"
include "biimpcd.mm"
include "adantr.mm"
include "imp.mm"
include "ianor.mm"
include "sylibr.mm"
include "3simpc.mm"
include "nn0zd.mm"
include "0z.mm"
include "jctil.mm"
include "3ad2ant1.mm"
include "syl2an.mm"
include "3adant1.mm"
include "biimprcd.mm"
include "ssfzo12bi.mm"
include "syl3anc.mm"
include "mtbird.mm"
include "wrddm.mm"
include "sseq2d.mm"
include "notbid.mm"
include "mpbird.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "exp31.mm"
include "impcom.mm"
include "jaoi3.mm"
include "orcoms.mm"
include "sylbi.mm"

theorem swrdnd
  let cF: class F
  let cL: class L
  let cV: class V
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word V /\ F e. ZZ /\ L e. ZZ ) -> ( ( F < 0 \/ L <_ F \/ ( # ` W ) < L ) -> ( W substr <. F , L >. ) = (/) ) )

  proof
    cF
    cc0
    clt
    wbr
    #
    cL
    cF
    cle
    wbr
    #
    cW
    chash
    cfv
    #
    cL
    clt
    wbr
    #
    w3o
    #
    cW
    cV
    cword
    #
    wcel
    #
    cF
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    w3a
    #
    cW
    cF
    cL
    cop
    csubstr
    co
    #
    c0
    wceq
    #
    @4
    @0
    @3
    wo
    #
    @1
    wo
    #
    @9
    @11
    wi
    #
    @4
    @0
    @3
    @1
    w3o
    @13
    @0
    @1
    @3
    3orcomb
    @0
    @3
    @1
    df-3or
    bitri
    @1
    @12
    @14
    @1
    @14
    @12
    @9
    @1
    @11
    cF
    cL
    cV
    cW
    swrdlend
    com12
    @12
    @1
    wn
    #
    @14
    @12
    @15
    @9
    @11
    @12
    @15
    wa
    #
    @9
    wa
    #
    @10
    cF
    cL
    cfzo
    co
    #
    cW
    cdm
    #
    wss
    #
    vi
    cc0
    cL
    cF
    cmin
    co
    cfzo
    co
    vi
    cv
    cF
    caddc
    co
    cW
    cfv
    cmpt
    #
    c0
    cif
    #
    c0
    @9
    @10
    @22
    wceq
    @16
    vi
    cW
    cF
    cL
    @5
    swrdval
    adantl
    @17
    @20
    @21
    c0
    @17
    @20
    wn
    #
    @18
    cc0
    @2
    cfzo
    co
    #
    wss
    #
    wn
    #
    @17
    @25
    cc0
    cF
    cle
    wbr
    #
    cL
    @2
    cle
    wbr
    #
    wa
    #
    @17
    @27
    wn
    #
    @28
    wn
    #
    wo
    #
    @29
    wn
    @16
    @9
    @32
    @12
    @9
    @32
    wi
    @15
    @9
    @12
    @32
    @9
    @0
    @30
    @3
    @31
    @7
    @6
    @0
    @30
    wb
    @8
    @7
    cF
    cc0
    cF
    zre
    #
    @7
    0red
    ltnled
    3ad2ant2
    @9
    @2
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    wa
    #
    @3
    @31
    wb
    @6
    @8
    @36
    @7
    @6
    @34
    @8
    @35
    @6
    @2
    cV
    cW
    lencl
    #
    nn0red
    cL
    zre
    #
    anim12i
    3adant2
    @2
    cL
    ltnle
    syl
    orbi12d
    biimpcd
    adantr
    imp
    @27
    @28
    ianor
    sylibr
    @17
    @7
    @8
    wa
    #
    cc0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    cF
    cL
    clt
    wbr
    #
    @25
    @29
    wb
    @9
    @39
    @16
    @6
    @7
    @8
    3simpc
    adantl
    @9
    @42
    @16
    @6
    @7
    @42
    @8
    @6
    @41
    @40
    @6
    @2
    @37
    nn0zd
    0z
    jctil
    3ad2ant1
    adantl
    @16
    @9
    @43
    @15
    @9
    @43
    wi
    @12
    @9
    @43
    @15
    @7
    @8
    @43
    @15
    wb
    #
    @6
    @7
    cF
    cr
    wcel
    @35
    @44
    @8
    @33
    @38
    cF
    cL
    ltnle
    syl2an
    3adant1
    biimprcd
    adantl
    imp
    cF
    cL
    cc0
    @2
    ssfzo12bi
    syl3anc
    mtbird
    @9
    @23
    @26
    wb
    #
    @16
    @6
    @7
    @45
    @8
    @6
    @20
    @25
    @6
    @19
    @24
    @18
    cV
    cW
    wrddm
    sseq2d
    notbid
    3ad2ant1
    adantl
    mpbird
    iffalsed
    eqtrd
    exp31
    impcom
    jaoi3
    orcoms
    sylbi
    com12
end
