include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cfz.mm"
include "cv.mm"
include "cneg.mm"
include "cprod.mm"
include "cexp.mm"
include "cabs.mm"
include "cle.mm"
include "clt.mm"
include "wn.mm"
include "faccld.mm"
include "nnred.mm"
include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wa.mm"
include "cz.mm"
include "nnzd.mm"
include "jca.mm"
include "adantr.mm"
include "simpr.mm"
include "dvdsle.mm"
include "sylc.mm"
include "mtand.mm"
include "cn0.mm"
include "wceq.mm"
include "fprodfac.mm"
include "wtru.mm"
include "fzfid.mm"
include "cc.mm"
include "elfzelz.mm"
include "znegcld.mm"
include "zcnd.mm"
include "adantl.mm"
include "fprodabs2.mm"
include "trud.mm"
include "absnegd.mm"
include "zred.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "ltled.mm"
include "absidd.mm"
include "eqtrd.mm"
include "prodeq2i.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "breq2d.mm"
include "mtbird.mm"
include "wb.mm"
include "fprodzcl.mm"
include "dvdsabsb.mm"
include "syl2anc.mm"
include "prmdvdsexp.mm"
include "syl3anc.mm"
include "cmul.mm"
include "csu.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cif.mm"
include "etransclem11.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "etransclem35.mm"
include "oveq1d.mm"
include "fprodcl.mm"
include "nnnn0d.mm"
include "expcld.mm"
include "nnm1nn0.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan3d.mm"

theorem etransclem41
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vj: setvar j
  let cF: class F
  let cM: class M
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m
  assume etransclem41.m: |- ( ph -> M e. NN0 )
  assume etransclem41.p: |- ( ph -> P e. Prime )
  assume etransclem41.mp: |- ( ph -> ( ! ` M ) < P )
  assume etransclem41.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )

  disjoint M j
  disjoint M x
  disjoint j x
  disjoint P j
  disjoint P x
  disjoint j ph
  disjoint ph x
  disjoint M c
  disjoint M d
  disjoint M k
  disjoint M n
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c x
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d x
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint j m
  disjoint m n
  disjoint m x
  disjoint P c
  disjoint P k
  disjoint P n
  disjoint c ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> -. P || ( ( ( ( RR Dn F ) ` ( P - 1 ) ) ` 0 ) / ( ! ` ( P - 1 ) ) ) )

  proof
    wph
    cP
    cc0
    cP
    c1
    cmin
    co
    #
    cr
    cF
    cdvn
    co
    cfv
    cfv
    #
    @0
    cfa
    cfv
    #
    cdiv
    co
    #
    cdvds
    wbr
    cP
    c1
    cM
    cfz
    co
    #
    vj
    cv
    #
    cneg
    #
    vj
    cprod
    #
    cP
    cexp
    co
    #
    cdvds
    wbr
    #
    wph
    @9
    cP
    @7
    cdvds
    wbr
    #
    wph
    @10
    cP
    @7
    cabs
    cfv
    #
    cdvds
    wbr
    #
    wph
    @12
    cP
    cM
    cfa
    cfv
    #
    cdvds
    wbr
    #
    wph
    @14
    cP
    @13
    cle
    wbr
    #
    wph
    @13
    cP
    clt
    wbr
    @15
    wn
    etransclem41.mp
    wph
    @13
    cP
    wph
    @13
    wph
    cM
    etransclem41.m
    faccld
    #
    nnred
    wph
    cP
    wph
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    etransclem41.p
    cP
    prmnn
    syl
    #
    nnred
    ltnled
    mpbid
    wph
    @14
    wa
    cP
    cz
    wcel
    #
    @13
    cn
    wcel
    #
    wa
    #
    @14
    @15
    wph
    @22
    @14
    wph
    @20
    @21
    wph
    cP
    @19
    nnzd
    #
    @16
    jca
    adantr
    wph
    @14
    simpr
    cP
    @13
    dvdsle
    sylc
    mtand
    wph
    @11
    @13
    cP
    cdvds
    wph
    @13
    @4
    @5
    vj
    cprod
    #
    @11
    wph
    cM
    cn0
    wcel
    @13
    @24
    wceq
    etransclem41.m
    cM
    vj
    fprodfac
    syl
    @11
    @4
    @6
    cabs
    cfv
    #
    vj
    cprod
    #
    @24
    @11
    @26
    wceq
    wtru
    @4
    @6
    vj
    wtru
    c1
    cM
    fzfid
    @5
    @4
    wcel
    #
    @6
    cc
    wcel
    #
    wtru
    @27
    @6
    @27
    @5
    @5
    c1
    cM
    elfzelz
    #
    znegcld
    #
    zcnd
    #
    adantl
    fprodabs2
    trud
    @4
    @25
    @5
    vj
    @27
    @25
    @5
    cabs
    cfv
    @5
    @27
    @5
    @27
    @5
    @29
    zcnd
    absnegd
    @27
    @5
    @27
    @5
    @29
    zred
    #
    @27
    cc0
    @5
    @27
    0red
    #
    @32
    @27
    cc0
    c1
    @5
    @33
    @27
    1red
    @32
    cc0
    c1
    clt
    wbr
    @27
    0lt1
    a1i
    @5
    c1
    cM
    elfzle1
    ltletrd
    ltled
    absidd
    eqtrd
    prodeq2i
    eqtri
    syl6reqr
    breq2d
    mtbird
    wph
    @20
    @7
    cz
    wcel
    #
    @10
    @12
    wb
    @23
    wph
    @4
    @6
    vj
    wph
    c1
    cM
    fzfid
    #
    @27
    @6
    cz
    wcel
    wph
    @30
    adantl
    fprodzcl
    #
    cP
    @7
    dvdsabsb
    syl2anc
    mtbird
    wph
    @17
    @34
    @18
    @9
    @10
    wb
    etransclem41.p
    @36
    @19
    @7
    cP
    cP
    prmdvdsexp
    syl3anc
    mtbird
    wph
    @3
    @8
    cP
    cdvds
    wph
    @3
    @2
    @8
    cmul
    co
    #
    @2
    cdiv
    co
    @8
    wph
    @1
    @37
    @2
    cdiv
    wph
    vx
    vm
    cn0
    cc0
    cM
    cfz
    co
    #
    vk
    cv
    #
    vd
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    vd
    cc0
    @40
    cfz
    co
    @38
    cmap
    co
    crab
    cmpt
    vk
    @38
    @39
    cc0
    wceq
    #
    @0
    cc0
    cif
    #
    cmpt
    cP
    vj
    vn
    cF
    cM
    vc
    @19
    etransclem41.m
    etransclem41.f
    vk
    vj
    vn
    vm
    cM
    vd
    vc
    etransclem11
    vk
    vj
    @38
    @42
    @5
    cc0
    wceq
    #
    @0
    cc0
    cif
    @39
    @5
    wceq
    @41
    @43
    @0
    cc0
    @39
    @5
    cc0
    eqeq1
    ifbid
    cbvmptv
    etransclem35
    oveq1d
    wph
    @8
    @2
    wph
    @7
    cP
    wph
    @4
    @6
    vj
    @35
    @27
    @28
    wph
    @31
    adantl
    fprodcl
    wph
    cP
    @19
    nnnn0d
    expcld
    wph
    @2
    wph
    @0
    wph
    @18
    @0
    cn0
    wcel
    @19
    cP
    nnm1nn0
    syl
    faccld
    #
    nncnd
    wph
    @2
    @44
    nnne0d
    divcan3d
    eqtrd
    breq2d
    mtbird
end
