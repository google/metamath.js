include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cphi.mm"
include "cfv.mm"
include "csu.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "ciun.mm"
include "chash.mm"
include "cdiv.mm"
include "wa.mm"
include "breq1.mm"
include "elrab.mm"
include "cif.mm"
include "hashgcdeq.mm"
include "adantrr.mm"
include "iftrue.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "sylan2b.mm"
include "sumeq2dv.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfi.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "sylancr.mm"
include "fzofi.mm"
include "ssrab2.mm"
include "mp2an.mm"
include "a1i.mm"
include "wral.mm"
include "wdisj.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "simprbi.mm"
include "rgen.mm"
include "rgenw.mm"
include "invdisj.mm"
include "mp1i.mm"
include "hashiun.mm"
include "cmpt.mm"
include "fveq2.mm"
include "eqid.mm"
include "dvdsflip.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "elrabi.mm"
include "phicld.mm"
include "nncnd.mm"
include "fsumf1o.mm"
include "3eqtr4rd.mm"
include "wrex.mm"
include "cz.mm"
include "wn.mm"
include "elfzoelz.mm"
include "nnz.mm"
include "adantr.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simprd.mm"
include "sylanbrc.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "iunrab.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "cn0.mm"
include "nnnn0.mm"
include "hashfzo0.mm"
include "syl.mm"

theorem phisum
  let vx: setvar x
  let cN: class N
  let vd: setvar d
  let vz: setvar z
  let cM: class M
  let vy: setvar y
  let vw: setvar w

  disjoint N x
  disjoint d x
  disjoint N d
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint N z
  disjoint y z
  disjoint M y
  disjoint N y
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint N w
  disjoint x y
  assert |- ( N e. NN -> sum_ d e. { x e. NN | x || N } ( phi ` d ) = N )

  proof
    cN
    cn
    wcel
    #
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vd
    cv
    #
    cphi
    cfv
    #
    vd
    csu
    #
    vy
    @3
    vz
    cv
    #
    cN
    cgcd
    co
    #
    vy
    cv
    #
    wceq
    #
    vz
    cc0
    cN
    cfzo
    co
    #
    crab
    #
    ciun
    #
    chash
    cfv
    #
    cN
    @0
    @3
    @12
    chash
    cfv
    #
    vy
    csu
    @3
    cN
    @9
    cdiv
    co
    #
    cphi
    cfv
    #
    vy
    csu
    @14
    @6
    @0
    @3
    @15
    @17
    vy
    @9
    @3
    wcel
    #
    @0
    @9
    cn
    wcel
    #
    @9
    cN
    cdvds
    wbr
    #
    wa
    #
    @15
    @17
    wceq
    @2
    @20
    vx
    @9
    cn
    @1
    @9
    cN
    cdvds
    breq1
    elrab
    @0
    @21
    wa
    @15
    @20
    @17
    cc0
    cif
    #
    @17
    @0
    @19
    @15
    @22
    wceq
    @20
    vz
    cN
    @9
    hashgcdeq
    adantrr
    @20
    @22
    @17
    wceq
    @0
    @19
    @20
    @17
    cc0
    iftrue
    ad2antll
    eqtrd
    sylan2b
    sumeq2dv
    @0
    vy
    @3
    @12
    @0
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    @3
    @23
    wss
    @3
    cfn
    wcel
    c1
    cN
    fzfi
    cN
    vx
    dvdsssfz1
    @23
    @3
    ssfi
    sylancr
    #
    @12
    cfn
    wcel
    #
    @0
    @18
    wa
    @11
    cfn
    wcel
    @12
    @11
    wss
    @25
    cc0
    cN
    fzofi
    @10
    vz
    @11
    ssrab2
    @11
    @12
    ssfi
    mp2an
    a1i
    vw
    cv
    #
    cN
    cgcd
    co
    #
    @9
    wceq
    #
    vw
    @12
    wral
    #
    vy
    @3
    wral
    vy
    @3
    @12
    wdisj
    @0
    @29
    vy
    @3
    @28
    vw
    @12
    @26
    @12
    wcel
    @26
    @11
    wcel
    @28
    @10
    @28
    vz
    @26
    @11
    @7
    @26
    wceq
    @8
    @27
    @9
    @7
    @26
    cN
    cgcd
    oveq1
    eqeq1d
    elrab
    simprbi
    rgen
    rgenw
    vy
    vw
    @3
    @12
    @27
    invdisj
    mp1i
    hashiun
    @0
    @3
    @5
    @3
    @17
    vd
    vy
    vz
    @3
    cN
    @7
    cdiv
    co
    #
    cmpt
    #
    @16
    @4
    @16
    cphi
    fveq2
    @24
    vx
    vz
    @3
    @31
    cN
    @3
    eqid
    @31
    eqid
    #
    dvdsflip
    @18
    @9
    @31
    cfv
    @16
    wceq
    @0
    vz
    @9
    @30
    @16
    @3
    @31
    @7
    @9
    cN
    cdiv
    oveq2
    @32
    cN
    @9
    cdiv
    ovex
    fvmpt
    adantl
    @0
    @4
    @3
    wcel
    #
    wa
    #
    @5
    @34
    @4
    @33
    @4
    cn
    wcel
    @0
    @2
    vx
    @4
    cn
    elrabi
    adantl
    phicld
    nncnd
    fsumf1o
    3eqtr4rd
    @0
    @14
    @11
    chash
    cfv
    #
    cN
    @0
    @13
    @11
    chash
    @0
    @11
    @10
    vy
    @3
    wrex
    #
    vz
    @11
    crab
    #
    @13
    @0
    @36
    vz
    @11
    wral
    @11
    @37
    wceq
    @0
    @36
    vz
    @11
    @0
    @7
    @11
    wcel
    #
    wa
    #
    @8
    @3
    wcel
    #
    @36
    @39
    @8
    cn
    wcel
    #
    @8
    cN
    cdvds
    wbr
    #
    @40
    @39
    @7
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @7
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    wn
    #
    @41
    @38
    @43
    @0
    @7
    cc0
    cN
    elfzoelz
    adantl
    #
    @0
    @44
    @38
    cN
    nnz
    adantr
    #
    @0
    @47
    @38
    @0
    @46
    @45
    @0
    cN
    cc0
    cN
    nnne0
    neneqd
    intnand
    adantr
    @7
    cN
    gcdn0cl
    syl21anc
    @39
    @8
    @7
    cdvds
    wbr
    #
    @42
    @39
    @43
    @44
    @50
    @42
    wa
    @48
    @49
    @7
    cN
    gcddvds
    syl2anc
    simprd
    @2
    @42
    vx
    @8
    cn
    @1
    @8
    cN
    cdvds
    breq1
    elrab
    sylanbrc
    @40
    @9
    @8
    wceq
    #
    vy
    @3
    wrex
    @36
    vy
    @8
    @3
    risset
    @51
    @10
    vy
    @3
    @9
    @8
    eqcom
    rexbii
    bitri
    sylib
    ralrimiva
    @36
    vz
    @11
    rabid2
    sylibr
    @10
    vy
    vz
    @3
    @11
    iunrab
    syl6reqr
    fveq2d
    @0
    cN
    cn0
    wcel
    @35
    cN
    wceq
    cN
    nnnn0
    cN
    hashfzo0
    syl
    eqtrd
    eqtrd
end
