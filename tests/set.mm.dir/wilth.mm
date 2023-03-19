include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfa.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "prmuz2.mm"
include "cv.mm"
include "cexp.mm"
include "cmo.mm"
include "wral.mm"
include "cfz.mm"
include "cpw.mm"
include "crab.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "eqid.mm"
include "weq.mm"
include "eleq2.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "raleqbi1dv.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "wilthlem3.mm"
include "jca.mm"
include "wn.mm"
include "simpl.mm"
include "cn.mm"
include "elfzuz.mm"
include "adantl.mm"
include "eluz2nn.mm"
include "syl.mm"
include "elfzuz3.mm"
include "dvdsfac.mm"
include "syl2anc.mm"
include "cz.mm"
include "clt.mm"
include "wi.mm"
include "cn0.mm"
include "ad2antrr.mm"
include "nnm1nn0.mm"
include "faccl.mm"
include "3syl.mm"
include "nnzd.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "ndvdsp1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "simplr.mm"
include "peano2zd.mm"
include "dvdstr.mm"
include "mpan2d.mm"
include "mtod.mm"
include "ralrimiva.mm"
include "isprm3.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem wilth
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( N e. Prime <-> ( N e. ( ZZ>= ` 2 ) /\ N || ( ( ! ` ( N - 1 ) ) + 1 ) ) )

  proof
    cN
    cprime
    wcel
    #
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cN
    c1
    cmin
    co
    #
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @0
    @2
    @6
    cN
    prmuz2
    vx
    vy
    @3
    vz
    cv
    #
    wcel
    #
    vn
    cv
    #
    cN
    c2
    cmin
    co
    #
    cexp
    co
    #
    cN
    cmo
    co
    #
    @8
    wcel
    #
    vn
    @8
    wral
    #
    wa
    #
    vz
    c1
    @3
    cfz
    co
    cpw
    #
    crab
    cN
    ccnfld
    cmgp
    cfv
    #
    @18
    eqid
    @16
    @3
    vx
    cv
    #
    wcel
    #
    vy
    cv
    #
    @11
    cexp
    co
    #
    cN
    cmo
    co
    #
    @19
    wcel
    #
    vy
    @19
    wral
    #
    wa
    vz
    vx
    @17
    vz
    vx
    weq
    #
    @9
    @20
    @15
    @25
    @8
    @19
    @3
    eleq2
    @15
    @23
    @8
    wcel
    #
    vy
    @8
    wral
    @26
    @25
    @14
    @27
    vn
    vy
    @8
    vn
    vy
    weq
    #
    @13
    @23
    @8
    @28
    @12
    @22
    cN
    cmo
    @10
    @21
    @11
    cexp
    oveq1
    oveq1d
    eleq1d
    cbvralv
    @27
    @24
    vy
    @8
    @19
    @8
    @19
    @23
    eleq2
    raleqbi1dv
    syl5bb
    anbi12d
    cbvrabv
    wilthlem3
    jca
    @7
    @2
    @10
    cN
    cdvds
    wbr
    #
    wn
    #
    vn
    c2
    @3
    cfz
    co
    #
    wral
    @0
    @2
    @6
    simpl
    @7
    @30
    vn
    @31
    @7
    @10
    @31
    wcel
    #
    wa
    #
    @29
    @10
    @5
    cdvds
    wbr
    #
    @33
    @10
    @4
    cdvds
    wbr
    #
    @34
    wn
    #
    @33
    @10
    cn
    wcel
    #
    @3
    @10
    cuz
    cfv
    wcel
    #
    @35
    @33
    @10
    @1
    wcel
    #
    @37
    @32
    @39
    @7
    @10
    c2
    @3
    elfzuz
    adantl
    #
    @10
    eluz2nn
    syl
    #
    @32
    @38
    @7
    @10
    c2
    @3
    elfzuz3
    adantl
    @10
    @3
    dvdsfac
    syl2anc
    @33
    @4
    cz
    wcel
    @37
    c1
    @10
    clt
    wbr
    #
    @35
    @36
    wi
    @33
    @4
    @33
    cN
    cn
    wcel
    #
    @3
    cn0
    wcel
    @4
    cn
    wcel
    @2
    @43
    @6
    @32
    cN
    eluz2nn
    ad2antrr
    #
    cN
    nnm1nn0
    @3
    faccl
    3syl
    nnzd
    #
    @41
    @33
    @39
    @42
    @40
    @39
    @37
    @42
    @10
    eluz2b2
    simprbi
    syl
    @10
    @4
    ndvdsp1
    syl3anc
    mpd
    @33
    @29
    @6
    @34
    @2
    @6
    @32
    simplr
    @33
    @10
    cz
    wcel
    cN
    cz
    wcel
    @5
    cz
    wcel
    @29
    @6
    wa
    @34
    wi
    @33
    @10
    @41
    nnzd
    @33
    cN
    @44
    nnzd
    @33
    @4
    @45
    peano2zd
    @10
    cN
    @5
    dvdstr
    syl3anc
    mpan2d
    mtod
    ralrimiva
    vn
    cN
    isprm3
    sylanbrc
    impbii
end
