include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "ccht.mm"
include "cfv.mm"
include "ce.mm"
include "cdvds.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cmin.mm"
include "cn.mm"
include "cc.mm"
include "wceq.mm"
include "chtcl.mm"
include "3ad2ant2.mm"
include "recnd.mm"
include "3ad2ant1.mm"
include "efsub.mm"
include "syl2anc.mm"
include "cv.mm"
include "crab.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "cprime.mm"
include "cin.mm"
include "clog.mm"
include "csu.mm"
include "chtfl.mm"
include "oveq12d.mm"
include "cuz.mm"
include "flword2.mm"
include "chtdif.mm"
include "syl.mm"
include "eqtr3d.mm"
include "wss.mm"
include "ssrab2.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "wa.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "simpll.mm"
include "simprl.mm"
include "readdcld.mm"
include "cmul.mm"
include "efadd.mm"
include "nnmulcl.mm"
include "ad2ant2l.mm"
include "eqeltrd.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "adantl.mm"
include "cfn.mm"
include "fzfid.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "reeflogd.mm"
include "cc0.mm"
include "0re.mm"
include "1nn.mm"
include "ef0.mm"
include "syl6eq.mm"
include "mpbir2an.mm"
include "fsumcllem.mm"
include "simprbi.mm"
include "eqeltrrd.mm"
include "nnzd.mm"
include "wne.mm"
include "wb.mm"
include "efchtcl.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem efchtdvds
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cP: class P


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( exp ` ( theta ` A ) ) || ( exp ` ( theta ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    ccht
    cfv
    #
    ce
    cfv
    #
    cB
    ccht
    cfv
    #
    ce
    cfv
    #
    cdvds
    wbr
    #
    @7
    @5
    cdiv
    co
    #
    cz
    wcel
    #
    @3
    @9
    @3
    @6
    @4
    cmin
    co
    #
    ce
    cfv
    #
    @9
    cn
    @3
    @6
    cc
    wcel
    @4
    cc
    wcel
    @12
    @9
    wceq
    @3
    @6
    @1
    @0
    @6
    cr
    wcel
    @2
    cB
    chtcl
    3ad2ant2
    recnd
    @3
    @4
    @0
    @1
    @4
    cr
    wcel
    @2
    cA
    chtcl
    3ad2ant1
    recnd
    @6
    @4
    efsub
    syl2anc
    @3
    @11
    vx
    cv
    #
    ce
    cfv
    #
    cn
    wcel
    #
    vx
    cr
    crab
    #
    wcel
    #
    @12
    cn
    wcel
    #
    @3
    @11
    cA
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cB
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    #
    @16
    @3
    @21
    ccht
    cfv
    #
    @19
    ccht
    cfv
    #
    cmin
    co
    #
    @11
    @26
    @3
    @27
    @6
    @28
    @4
    cmin
    @1
    @0
    @27
    @6
    wceq
    @2
    cB
    chtfl
    3ad2ant2
    @0
    @1
    @28
    @4
    wceq
    @2
    cA
    chtfl
    3ad2ant1
    oveq12d
    @3
    @21
    @19
    cuz
    cfv
    wcel
    @29
    @26
    wceq
    cA
    cB
    flword2
    @19
    @21
    vp
    chtdif
    syl
    eqtr3d
    @3
    vy
    vz
    @23
    @25
    @16
    vp
    @16
    cc
    wss
    @3
    @16
    cr
    cc
    @15
    vx
    cr
    ssrab2
    ax-resscn
    sstri
    a1i
    vy
    cv
    #
    @16
    wcel
    #
    vz
    cv
    #
    @16
    wcel
    #
    wa
    @30
    @32
    caddc
    co
    #
    @16
    wcel
    #
    @3
    @31
    @30
    cr
    wcel
    #
    @30
    ce
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @32
    cr
    wcel
    #
    @32
    ce
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @35
    @33
    @15
    @38
    vx
    @30
    cr
    @13
    @30
    wceq
    @14
    @37
    cn
    @13
    @30
    ce
    fveq2
    eleq1d
    elrab
    @15
    @42
    vx
    @32
    cr
    @13
    @32
    wceq
    @14
    @41
    cn
    @13
    @32
    ce
    fveq2
    eleq1d
    elrab
    @39
    @43
    wa
    #
    @34
    cr
    wcel
    @34
    ce
    cfv
    #
    cn
    wcel
    #
    @35
    @44
    @30
    @32
    @36
    @38
    @43
    simpll
    #
    @39
    @40
    @42
    simprl
    #
    readdcld
    @44
    @45
    @37
    @41
    cmul
    co
    #
    cn
    @44
    @30
    cc
    wcel
    @32
    cc
    wcel
    @45
    @49
    wceq
    @44
    @30
    @47
    recnd
    @44
    @32
    @48
    recnd
    @30
    @32
    efadd
    syl2anc
    @38
    @42
    @49
    cn
    wcel
    @36
    @40
    @37
    @41
    nnmulcl
    ad2ant2l
    eqeltrd
    @15
    @46
    vx
    @34
    cr
    @13
    @34
    wceq
    @14
    @45
    cn
    @13
    @34
    ce
    fveq2
    eleq1d
    elrab
    sylanbrc
    syl2anb
    adantl
    @3
    @22
    cfn
    wcel
    @23
    @22
    wss
    @23
    cfn
    wcel
    @3
    @20
    @21
    fzfid
    @22
    cprime
    inss1
    @22
    @23
    ssfi
    sylancl
    @3
    @24
    @23
    wcel
    #
    wa
    #
    @25
    cr
    wcel
    @25
    ce
    cfv
    #
    cn
    wcel
    #
    @25
    @16
    wcel
    @51
    @24
    @51
    @24
    @51
    @24
    cprime
    wcel
    @24
    cn
    wcel
    @51
    @23
    cprime
    @24
    @22
    cprime
    inss2
    @3
    @50
    simpr
    sseldi
    @24
    prmnn
    syl
    #
    nnrpd
    #
    relogcld
    @51
    @52
    @24
    cn
    @51
    @24
    @55
    reeflogd
    @54
    eqeltrd
    @15
    @53
    vx
    @25
    cr
    @13
    @25
    wceq
    @14
    @52
    cn
    @13
    @25
    ce
    fveq2
    eleq1d
    elrab
    sylanbrc
    cc0
    @16
    wcel
    #
    @3
    @56
    cc0
    cr
    wcel
    c1
    cn
    wcel
    #
    0re
    1nn
    @15
    @57
    vx
    cc0
    cr
    @13
    cc0
    wceq
    #
    @14
    c1
    cn
    @58
    @14
    cc0
    ce
    cfv
    c1
    @13
    cc0
    ce
    fveq2
    ef0
    syl6eq
    eleq1d
    elrab
    mpbir2an
    a1i
    fsumcllem
    eqeltrd
    @17
    @11
    cr
    wcel
    @18
    @15
    @18
    vx
    @11
    cr
    @13
    @11
    wceq
    @14
    @12
    cn
    @13
    @11
    ce
    fveq2
    eleq1d
    elrab
    simprbi
    syl
    eqeltrrd
    nnzd
    @3
    @5
    cz
    wcel
    @5
    cc0
    wne
    @7
    cz
    wcel
    @8
    @10
    wb
    @3
    @5
    @0
    @1
    @5
    cn
    wcel
    @2
    cA
    efchtcl
    3ad2ant1
    #
    nnzd
    @3
    @5
    @59
    nnne0d
    @3
    @7
    @1
    @0
    @7
    cn
    wcel
    @2
    cB
    efchtcl
    3ad2ant2
    nnzd
    @5
    @7
    dvdsval2
    syl3anc
    mpbird
end
