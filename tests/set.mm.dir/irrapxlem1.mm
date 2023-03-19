include "crp.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cmul.mm"
include "cmo.mm"
include "cfl.mm"
include "cfv.mm"
include "cr.mm"
include "wss.mm"
include "cuz.mm"
include "fzssuz.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "ovexd.mm"
include "clt.mm"
include "wbr.mm"
include "csdm.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "adantl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nnz.mm"
include "nnre.mm"
include "ltm1d.mm"
include "fzsdom2.mm"
include "syl21anc.mm"
include "cle.mm"
include "ad2antlr.mm"
include "rpre.mm"
include "ad2antrr.mm"
include "elfzelz.mm"
include "zred.mm"
include "remulcld.mm"
include "1rp.mm"
include "modcl.mm"
include "sylancl.mm"
include "flcld.mm"
include "wn.mm"
include "recnd.mm"
include "mul01d.mm"
include "modge0.mm"
include "wb.mm"
include "0red.mm"
include "nngt0.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "lenltd.mm"
include "0z.mm"
include "fllt.mm"
include "mtbid.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "caddc.mm"
include "flle.mm"
include "syl.mm"
include "modlt.mm"
include "1red.mm"
include "ltmul2.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "lelttrd.mm"
include "wceq.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "breqtrrd.mm"
include "1z.mm"
include "zsubcl.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "fphpdo.mm"

theorem irrapxlem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. ( 0 ... B ) ( x < y /\ ( |_ ` ( B x. ( ( A x. x ) mod 1 ) ) ) = ( |_ ` ( B x. ( ( A x. y ) mod 1 ) ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    vx
    vy
    va
    cc0
    cB
    cfz
    co
    #
    cc0
    cB
    c1
    cmin
    co
    #
    cfz
    co
    #
    cB
    cA
    va
    cv
    #
    cmul
    co
    #
    c1
    cmo
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cA
    vx
    cv
    #
    cmul
    co
    #
    c1
    cmo
    co
    #
    cmul
    co
    #
    cfl
    cfv
    cB
    cA
    vy
    cv
    #
    cmul
    co
    #
    c1
    cmo
    co
    #
    cmul
    co
    #
    cfl
    cfv
    @3
    cr
    wss
    @2
    @3
    cc0
    cuz
    cfv
    #
    cr
    cc0
    cB
    fzssuz
    @19
    cz
    cr
    cc0
    uzssz
    zssre
    sstri
    sstri
    a1i
    @2
    cc0
    @4
    cfz
    ovexd
    @2
    @4
    @19
    wcel
    cB
    cz
    wcel
    #
    @4
    cB
    clt
    wbr
    @5
    @3
    csdm
    wbr
    @2
    @4
    cn0
    @19
    @1
    @4
    cn0
    wcel
    #
    @0
    cB
    nnm1nn0
    #
    adantl
    nn0uz
    syl6eleq
    @1
    @20
    @0
    cB
    nnz
    #
    adantl
    @2
    cB
    @1
    cB
    cr
    wcel
    #
    @0
    cB
    nnre
    #
    adantl
    ltm1d
    cc0
    @4
    cB
    fzsdom2
    syl21anc
    @2
    @6
    @3
    wcel
    #
    wa
    #
    @10
    cn0
    wcel
    #
    @21
    @10
    @4
    cle
    wbr
    #
    @10
    @5
    wcel
    @27
    @10
    cz
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    @28
    @27
    @9
    @27
    cB
    @8
    @1
    @24
    @0
    @26
    @25
    ad2antlr
    #
    @27
    @7
    cr
    wcel
    #
    c1
    crp
    wcel
    #
    @8
    cr
    wcel
    #
    @27
    cA
    @6
    @0
    cA
    cr
    wcel
    @1
    @26
    cA
    rpre
    ad2antrr
    @26
    @6
    cr
    wcel
    @2
    @26
    @6
    @6
    cc0
    cB
    elfzelz
    zred
    adantl
    remulcld
    #
    1rp
    @7
    c1
    modcl
    sylancl
    #
    remulcld
    #
    flcld
    #
    @27
    @31
    @10
    cc0
    clt
    wbr
    #
    wn
    @27
    @9
    cc0
    clt
    wbr
    #
    @40
    @27
    cc0
    @9
    cle
    wbr
    @41
    wn
    @27
    cB
    cc0
    cmul
    co
    #
    cc0
    @9
    cle
    @27
    cB
    @27
    cB
    @32
    recnd
    #
    mul01d
    @27
    cc0
    @8
    cle
    wbr
    #
    @42
    @9
    cle
    wbr
    #
    @27
    @33
    @34
    @44
    @36
    1rp
    @7
    c1
    modge0
    sylancl
    @27
    cc0
    cr
    wcel
    @35
    @24
    cc0
    cB
    clt
    wbr
    #
    @44
    @45
    wb
    @27
    0red
    #
    @37
    @32
    @1
    @46
    @0
    @26
    cB
    nngt0
    ad2antlr
    #
    cc0
    @8
    cB
    lemul2
    syl112anc
    mpbid
    eqbrtrrd
    @27
    cc0
    @9
    @47
    @38
    lenltd
    mpbid
    @27
    @9
    cr
    wcel
    #
    cc0
    cz
    wcel
    @41
    @40
    wb
    @38
    0z
    @9
    cc0
    fllt
    sylancl
    mtbid
    @27
    cc0
    @10
    @47
    @27
    @10
    @39
    zred
    #
    lenltd
    mpbird
    @10
    elnn0z
    sylanbrc
    @1
    @21
    @0
    @26
    @22
    ad2antlr
    @27
    @29
    @10
    @4
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @27
    @10
    cB
    @51
    clt
    @27
    @10
    @9
    cB
    @50
    @38
    @32
    @27
    @49
    @10
    @9
    cle
    wbr
    @38
    @9
    flle
    syl
    @27
    @9
    cB
    c1
    cmul
    co
    #
    cB
    clt
    @27
    @8
    c1
    clt
    wbr
    #
    @9
    @53
    clt
    wbr
    #
    @27
    @33
    @34
    @54
    @36
    1rp
    @7
    c1
    modlt
    sylancl
    @27
    @35
    c1
    cr
    wcel
    @24
    @46
    @54
    @55
    wb
    @37
    @27
    1red
    @32
    @48
    @8
    c1
    cB
    ltmul2
    syl112anc
    mpbid
    @27
    cB
    @43
    mulid1d
    breqtrd
    lelttrd
    @1
    @51
    cB
    wceq
    #
    @0
    @26
    @1
    cB
    cc
    wcel
    c1
    cc
    wcel
    @56
    cB
    nncn
    ax-1cn
    cB
    c1
    npcan
    sylancl
    ad2antlr
    breqtrrd
    @27
    @30
    @4
    cz
    wcel
    #
    @29
    @52
    wb
    @39
    @27
    @20
    c1
    cz
    wcel
    @57
    @1
    @20
    @0
    @26
    @23
    ad2antlr
    1z
    cB
    c1
    zsubcl
    sylancl
    @10
    @4
    zleltp1
    syl2anc
    mpbird
    @10
    @4
    elfz2nn0
    syl3anbrc
    @6
    @11
    wceq
    #
    @9
    @14
    cfl
    @58
    @8
    @13
    cB
    cmul
    @58
    @7
    @12
    c1
    cmo
    @6
    @11
    cA
    cmul
    oveq2
    oveq1d
    oveq2d
    fveq2d
    @6
    @15
    wceq
    #
    @9
    @18
    cfl
    @59
    @8
    @17
    cB
    cmul
    @59
    @7
    @16
    c1
    cmo
    @6
    @15
    cA
    cmul
    oveq2
    oveq1d
    oveq2d
    fveq2d
    fphpdo
end
