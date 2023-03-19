include "c2.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cfl.mm"
include "c3.mm"
include "cdiv.mm"
include "cfz.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "2nn.mm"
include "c5.mm"
include "5nn.mm"
include "eluznn.mm"
include "sylancr.mm"
include "nnmulcl.mm"
include "nnred.mm"
include "nnrpd.mm"
include "rpge0d.mm"
include "resqrtcld.mm"
include "flcld.mm"
include "c9.mm"
include "sqrt9.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cr.mm"
include "9re.mm"
include "a1i.mm"
include "10re.mm"
include "caddc.mm"
include "lep1.mm"
include "ax-mp.mm"
include "9p1e10.mm"
include "breqtri.mm"
include "5cn.mm"
include "2cn.mm"
include "5t2e10.mm"
include "mulcomli.mm"
include "eluzle.mm"
include "syl.mm"
include "wb.mm"
include "clt.mm"
include "wa.mm"
include "5re.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an13.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "letrd.mm"
include "0re.mm"
include "9pos.mm"
include "ltleii.mm"
include "rprege0d.mm"
include "sqrtle.mm"
include "3z.mm"
include "flge.mm"
include "sylancl.mm"
include "eluz1i.mm"
include "sylanbrc.mm"
include "3nn.mm"
include "nndivre.mm"
include "3re.mm"
include "sqrtgt0d.mm"
include "syl112anc.mm"
include "wceq.mm"
include "remsqsqrt.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "3pos.mm"
include "lemuldiv.mm"
include "syl3anc.mm"
include "flword2.mm"
include "elfzuzb.mm"
include "oveq2i.mm"
include "3eltr4g.mm"

theorem bposlem4
  let wph: wff ph
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume bpos.1: |- ( ph -> N e. ( ZZ>= ` 5 ) )
  assume bpos.2: |- ( ph -> -. E. p e. Prime ( N < p /\ p <_ ( 2 x. N ) ) )
  assume bpos.3: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ ( n pCnt ( ( 2 x. N ) _C N ) ) ) , 1 ) )
  assume bpos.4: |- K = ( |_ ` ( ( 2 x. N ) / 3 ) )
  assume bpos.5: |- M = ( |_ ` ( sqrt ` ( 2 x. N ) ) )

  disjoint F p
  disjoint n p
  disjoint K n
  disjoint K p
  disjoint M p
  disjoint N n
  disjoint N p
  disjoint n ph
  disjoint p ph
  disjoint k p
  disjoint k x
  disjoint F k
  disjoint p x
  disjoint F x
  disjoint M x
  disjoint k n
  disjoint N k
  disjoint n x
  disjoint N x
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> M e. ( 3 ... K ) )

  proof
    wph
    c2
    cN
    cmul
    co
    #
    csqrt
    cfv
    #
    cfl
    cfv
    #
    c3
    @0
    c3
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cM
    c3
    cK
    cfz
    co
    wph
    @2
    c3
    cuz
    cfv
    wcel
    #
    @4
    @2
    cuz
    cfv
    wcel
    #
    @2
    @5
    wcel
    wph
    @2
    cz
    wcel
    c3
    @2
    cle
    wbr
    #
    @6
    wph
    @1
    wph
    @0
    wph
    @0
    wph
    c2
    cn
    wcel
    cN
    cn
    wcel
    #
    @0
    cn
    wcel
    2nn
    wph
    c5
    cn
    wcel
    cN
    c5
    cuz
    cfv
    wcel
    #
    @9
    5nn
    bpos.1
    cN
    c5
    eluznn
    sylancr
    #
    c2
    cN
    nnmulcl
    sylancr
    #
    nnred
    #
    wph
    @0
    wph
    @0
    @12
    nnrpd
    #
    rpge0d
    #
    resqrtcld
    #
    flcld
    wph
    c3
    @1
    cle
    wbr
    #
    @8
    wph
    c3
    c9
    csqrt
    cfv
    #
    @1
    cle
    sqrt9
    wph
    c9
    @0
    cle
    wbr
    #
    @18
    @1
    cle
    wbr
    #
    wph
    c9
    c1
    cc0
    cdc
    #
    @0
    c9
    cr
    wcel
    #
    wph
    9re
    a1i
    @21
    cr
    wcel
    wph
    10re
    a1i
    @13
    c9
    @21
    cle
    wbr
    wph
    c9
    c9
    c1
    caddc
    co
    #
    @21
    cle
    @22
    c9
    @23
    cle
    wbr
    9re
    c9
    lep1
    ax-mp
    9p1e10
    breqtri
    a1i
    wph
    @21
    c2
    c5
    cmul
    co
    #
    @0
    cle
    c5
    c2
    @21
    5cn
    2cn
    5t2e10
    mulcomli
    wph
    c5
    cN
    cle
    wbr
    #
    @24
    @0
    cle
    wbr
    #
    wph
    @10
    @25
    bpos.1
    c5
    cN
    eluzle
    syl
    wph
    cN
    cr
    wcel
    #
    @25
    @26
    wb
    #
    wph
    cN
    @11
    nnred
    c5
    cr
    wcel
    @27
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    @28
    5re
    @29
    @30
    2re
    2pos
    pm3.2i
    c5
    cN
    c2
    lemul2
    mp3an13
    syl
    mpbid
    syl5eqbrr
    letrd
    wph
    @22
    cc0
    c9
    cle
    wbr
    #
    wa
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    wa
    @19
    @20
    wb
    @22
    @31
    9re
    cc0
    c9
    0re
    9re
    9pos
    ltleii
    pm3.2i
    wph
    @0
    @14
    rprege0d
    c9
    @0
    sqrtle
    sylancr
    mpbid
    syl5eqbrr
    #
    wph
    @1
    cr
    wcel
    #
    c3
    cz
    wcel
    @17
    @8
    wb
    @16
    3z
    @1
    c3
    flge
    sylancl
    mpbid
    c3
    @2
    3z
    eluz1i
    sylanbrc
    wph
    @35
    @3
    cr
    wcel
    #
    @1
    @3
    cle
    wbr
    #
    @7
    @16
    wph
    @32
    c3
    cn
    wcel
    @36
    @13
    3nn
    @0
    c3
    nndivre
    sylancl
    wph
    @1
    c3
    cmul
    co
    #
    @0
    cle
    wbr
    #
    @37
    wph
    @38
    @1
    @1
    cmul
    co
    #
    @0
    cle
    wph
    @17
    @38
    @40
    cle
    wbr
    #
    @34
    wph
    c3
    cr
    wcel
    #
    @35
    @35
    cc0
    @1
    clt
    wbr
    @17
    @41
    wb
    @42
    wph
    3re
    a1i
    @16
    @16
    wph
    @0
    @14
    sqrtgt0d
    c3
    @1
    @1
    lemul2
    syl112anc
    mpbid
    wph
    @32
    @33
    @40
    @0
    wceq
    @13
    @15
    @0
    remsqsqrt
    syl2anc
    breqtrd
    wph
    @35
    @32
    @42
    cc0
    c3
    clt
    wbr
    #
    wa
    #
    @39
    @37
    wb
    @16
    @13
    @44
    wph
    @42
    @43
    3re
    3pos
    pm3.2i
    a1i
    @1
    @0
    c3
    lemuldiv
    syl3anc
    mpbid
    @1
    @3
    flword2
    syl3anc
    @2
    c3
    @4
    elfzuzb
    sylanbrc
    bpos.5
    cK
    @4
    c3
    cfz
    bpos.4
    oveq2i
    3eltr4g
end
