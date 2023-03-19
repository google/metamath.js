include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cneg.mm"
include "ce.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "c3.mm"
include "cdc.mm"
include "2nn0.mm"
include "3nn0.mm"
include "deccl.mm"
include "eqeltri.mm"
include "c6.mm"
include "c5.mm"
include "6nn0.mm"
include "5nn.mm"
include "decnncl.mm"
include "birthdaylem3.mm"
include "mp2an.mm"
include "clog.mm"
include "log2ub.mm"
include "cmul.mm"
include "nn0cni.mm"
include "sqvali.mm"
include "mulid1i.mm"
include "eqcomi.mm"
include "oveq12i.mm"
include "ax-1cn.mm"
include "subdii.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "subcli.mm"
include "2cn.mm"
include "2ne0.mm"
include "divassi.mm"
include "1nn0.mm"
include "caddc.mm"
include "2p1e3.mm"
include "eqid.mm"
include "decsuc.mm"
include "pncan3oi.mm"
include "eqtri.mm"
include "wceq.mm"
include "cc0.mm"
include "0nn0.mm"
include "addid1i.mm"
include "dec0h.mm"
include "decmul2c.mm"
include "divmuli.mm"
include "mpbir.mm"
include "3p2e5.mm"
include "decaddi.mm"
include "breqtrri.mm"
include "crp.mm"
include "cr.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "5nn0.mm"
include "nn0rei.mm"
include "nndivre.mm"
include "ltnegi.mm"
include "mpbi.mm"
include "wb.mm"
include "renegcli.mm"
include "eflt.mm"
include "cc.mm"
include "recni.mm"
include "efneg.mm"
include "reeflog.mm"
include "oveq2i.mm"
include "breqtri.mm"
include "cfn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "birthdaylem1.mm"
include "simp2i.mm"
include "simp1i.mm"
include "ssfi.mm"
include "hashcl.mm"
include "simp3i.mm"
include "hashnncl.mm"
include "reefcl.mm"
include "halfre.mm"
include "lelttri.mm"

theorem birthday
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume birthday.s: |- S = { f | f : ( 1 ... K ) --> ( 1 ... N ) }
  assume birthday.t: |- T = { f | f : ( 1 ... K ) -1-1-> ( 1 ... N ) }
  assume birthday.k: |- K = ; 2 3
  assume birthday.n: |- N = ; ; 3 6 5

  disjoint K f
  disjoint N f
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  assert |- ( ( # ` T ) / ( # ` S ) ) < ( 1 / 2 )

  proof
    cT
    chash
    cfv
    #
    cS
    chash
    cfv
    #
    cdiv
    co
    #
    cK
    c2
    cexp
    co
    #
    cK
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cN
    cdiv
    co
    #
    cneg
    #
    ce
    cfv
    #
    cle
    wbr
    #
    @8
    c1
    c2
    cdiv
    co
    #
    clt
    wbr
    @2
    @10
    clt
    wbr
    cK
    cn0
    wcel
    cN
    cn
    wcel
    #
    @9
    cK
    c2
    c3
    cdc
    #
    cn0
    birthday.k
    c2
    c3
    2nn0
    3nn0
    deccl
    eqeltri
    #
    cN
    c3
    c6
    cdc
    #
    c5
    cdc
    #
    cn
    birthday.n
    @14
    c5
    c3
    c6
    3nn0
    6nn0
    deccl
    5nn
    decnncl
    eqeltri
    #
    cS
    cT
    vf
    cK
    cN
    birthday.s
    birthday.t
    birthdaylem3
    mp2an
    @8
    c2
    clog
    cfv
    #
    cneg
    #
    ce
    cfv
    #
    @10
    clt
    @7
    @18
    clt
    wbr
    #
    @8
    @19
    clt
    wbr
    #
    @17
    @6
    clt
    wbr
    @20
    @17
    c2
    c5
    cdc
    #
    c3
    cdc
    #
    @15
    cdiv
    co
    @6
    clt
    log2ub
    @5
    @23
    cN
    @15
    cdiv
    @5
    cK
    cK
    c1
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @23
    @4
    @25
    c2
    cdiv
    @4
    cK
    cK
    cmul
    co
    #
    cK
    c1
    cmul
    co
    #
    cmin
    co
    @25
    @3
    @27
    cK
    @28
    cmin
    cK
    cK
    @13
    nn0cni
    #
    sqvali
    @28
    cK
    cK
    @29
    mulid1i
    #
    eqcomi
    oveq12i
    cK
    cK
    c1
    @29
    @29
    ax-1cn
    subdii
    eqtr4i
    oveq1i
    @26
    cK
    @24
    c2
    cdiv
    co
    #
    cmul
    co
    @23
    cK
    @24
    c2
    @29
    cK
    c1
    @29
    ax-1cn
    subcli
    2cn
    2ne0
    divassi
    c1
    c1
    @22
    c3
    cK
    c2
    @31
    @13
    1nn0
    1nn0
    @31
    c2
    c2
    cdc
    #
    c2
    cdiv
    co
    #
    c1
    c1
    cdc
    #
    @24
    @32
    c2
    cdiv
    @24
    @32
    c1
    caddc
    co
    #
    c1
    cmin
    co
    @32
    cK
    @35
    c1
    cmin
    cK
    @12
    @35
    birthday.k
    c2
    c2
    c3
    @32
    2nn0
    2nn0
    2p1e3
    @32
    eqid
    decsuc
    eqtr4i
    oveq1i
    @32
    c1
    @32
    c2
    c2
    2nn0
    2nn0
    deccl
    nn0cni
    #
    ax-1cn
    pncan3oi
    eqtri
    oveq1i
    @33
    @34
    wceq
    c2
    @34
    cmul
    co
    @32
    wceq
    c1
    c1
    c2
    c2
    c2
    cc0
    @34
    2nn0
    1nn0
    1nn0
    @34
    eqid
    2nn0
    0nn0
    c2
    c1
    cmul
    co
    #
    cc0
    caddc
    co
    c2
    cc0
    caddc
    co
    c2
    @37
    c2
    cc0
    caddc
    c2
    2cn
    mulid1i
    #
    oveq1i
    c2
    2cn
    addid1i
    eqtri
    @37
    c2
    cc0
    c2
    cdc
    @38
    c2
    2nn0
    dec0h
    eqtri
    decmul2c
    @32
    c2
    @34
    @36
    2cn
    @34
    c1
    c1
    1nn0
    1nn0
    deccl
    nn0cni
    2ne0
    divmuli
    mpbir
    eqtri
    3nn0
    2nn0
    c2
    c3
    c5
    @28
    c2
    2nn0
    3nn0
    2nn0
    @28
    cK
    @12
    @30
    birthday.k
    eqtri
    #
    3p2e5
    decaddi
    @39
    decmul2c
    eqtri
    eqtri
    #
    birthday.n
    oveq12i
    breqtrri
    @17
    @6
    c2
    crp
    wcel
    #
    @17
    cr
    wcel
    2rp
    c2
    relogcl
    ax-mp
    #
    @5
    cr
    wcel
    @11
    @6
    cr
    wcel
    @5
    @5
    @23
    cn0
    @40
    @22
    c3
    c2
    c5
    2nn0
    5nn0
    deccl
    3nn0
    deccl
    eqeltri
    nn0rei
    @16
    @5
    cN
    nndivre
    mp2an
    #
    ltnegi
    mpbi
    @7
    cr
    wcel
    #
    @18
    cr
    wcel
    @20
    @21
    wb
    @6
    @43
    renegcli
    #
    @17
    @42
    renegcli
    @7
    @18
    eflt
    mp2an
    mpbi
    @19
    c1
    @17
    ce
    cfv
    #
    cdiv
    co
    #
    @10
    @17
    cc
    wcel
    @19
    @47
    wceq
    @17
    @42
    recni
    @17
    efneg
    ax-mp
    @46
    c2
    c1
    cdiv
    @41
    @46
    c2
    wceq
    2rp
    c2
    reeflog
    ax-mp
    oveq2i
    eqtri
    breqtri
    @2
    @8
    @10
    @0
    cr
    wcel
    @1
    cn
    wcel
    #
    @2
    cr
    wcel
    @0
    cT
    cfn
    wcel
    #
    @0
    cn0
    wcel
    cS
    cfn
    wcel
    #
    cT
    cS
    wss
    #
    @49
    @51
    @50
    @11
    cS
    c0
    wne
    #
    wi
    #
    cS
    cT
    vf
    cK
    cN
    birthday.s
    birthday.t
    birthdaylem1
    #
    simp2i
    #
    @51
    @50
    @53
    @54
    simp1i
    cS
    cT
    ssfi
    mp2an
    cT
    hashcl
    ax-mp
    nn0rei
    @48
    @52
    @11
    @52
    @16
    @51
    @50
    @53
    @54
    simp3i
    ax-mp
    @50
    @48
    @52
    wb
    @55
    cS
    hashnncl
    ax-mp
    mpbir
    @0
    @1
    nndivre
    mp2an
    @44
    @8
    cr
    wcel
    @45
    @7
    reefcl
    ax-mp
    halfre
    lelttri
    mp2an
end
