include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cmul.mm"
include "cdiv.mm"
include "csu.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cz.mm"
include "wtru.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "1red.mm"
include "wcel.mm"
include "wa.mm"
include "fzfid.mm"
include "cn.mm"
include "cc.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrp.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "peano2nn.mm"
include "nnmulcl.mm"
include "mpdan.mm"
include "nndivred.mm"
include "recnd.mm"
include "fsumcl.mm"
include "cmpt.mm"
include "co1.mm"
include "pntrsumo1.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "clt.mm"
include "adantr.mm"
include "adantlr.mm"
include "ad2ant2r.mm"
include "fsumabs.mm"
include "absge0d.mm"
include "cuz.mm"
include "simplr.mm"
include "simprll.mm"
include "simprr.mm"
include "ltled.mm"
include "flword2.mm"
include "syl3anc.mm"
include "fzss2.mm"
include "fsumless.mm"
include "letrd.mm"
include "o1bddrp.mm"
include "trud.mm"
include "wi.mm"
include "zre.mm"
include "imim1i.mm"
include "flid.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "mpbidi.mm"
include "ralimi2.mm"
include "reximi.mm"
include "ax-mp.mm"

theorem pntrsumbnd
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  let cA: class A
  let vb: setvar b
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a m
  disjoint a n
  disjoint m n
  disjoint c m
  disjoint c n
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint a d
  disjoint a k
  disjoint a x
  disjoint A a
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint c d
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint d y
  disjoint R d
  disjoint k y
  disjoint R k
  disjoint m y
  disjoint n y
  disjoint x y
  disjoint R x
  disjoint R y
  assert |- E. c e. RR+ A. m e. ZZ ( abs ` sum_ n e. ( 1 ... m ) ( ( R ` n ) / ( n x. ( n + 1 ) ) ) ) <_ c

  proof
    c1
    vm
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cR
    cfv
    #
    @3
    @3
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    vn
    csu
    #
    cabs
    cfv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vm
    cr
    wral
    #
    vc
    crp
    wrex
    #
    c1
    @0
    cfz
    co
    #
    @7
    vn
    csu
    #
    cabs
    cfv
    #
    @10
    cle
    wbr
    #
    vm
    cz
    wral
    #
    vc
    crp
    wrex
    @13
    wtru
    vm
    vx
    cr
    @8
    c1
    vc
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    cabs
    cfv
    #
    vn
    csu
    #
    cr
    cr
    wss
    wtru
    cr
    ssid
    a1i
    wtru
    1red
    wtru
    @0
    cr
    wcel
    #
    wa
    #
    @2
    @7
    vn
    @25
    c1
    @1
    fzfid
    @25
    @3
    @2
    wcel
    #
    wa
    @3
    cn
    wcel
    #
    @7
    cc
    wcel
    #
    @26
    @27
    @25
    @3
    @1
    elfznn
    adantl
    @27
    @7
    @27
    @4
    @6
    @27
    @3
    crp
    wcel
    @4
    cr
    wcel
    @3
    nnrp
    crp
    cr
    @3
    cR
    cR
    va
    pntrval.r
    pntrf
    ffvelrni
    syl
    @27
    @5
    cn
    wcel
    @6
    cn
    wcel
    @3
    peano2nn
    @3
    @5
    nnmulcl
    mpdan
    nndivred
    recnd
    #
    syl
    #
    fsumcl
    #
    vm
    cr
    @8
    cmpt
    co1
    wcel
    wtru
    vm
    cR
    vn
    va
    pntrval.r
    pntrsumo1
    a1i
    wtru
    @19
    cr
    wcel
    #
    c1
    @19
    cle
    wbr
    #
    wa
    #
    wa
    #
    @21
    @22
    vn
    @35
    c1
    @20
    fzfid
    @35
    @3
    @21
    wcel
    #
    wa
    #
    @7
    @37
    @27
    @28
    @36
    @27
    @35
    @3
    @20
    elfznn
    #
    adantl
    @29
    syl
    abscld
    fsumrecl
    #
    @25
    @34
    @0
    @19
    clt
    wbr
    #
    wa
    #
    wa
    #
    @9
    @2
    @22
    vn
    csu
    @23
    @42
    @8
    @25
    @8
    cc
    wcel
    @41
    @31
    adantr
    abscld
    @42
    @2
    @22
    vn
    @42
    c1
    @1
    fzfid
    #
    @42
    @26
    wa
    @7
    @25
    @26
    @28
    @41
    @30
    adantlr
    #
    abscld
    fsumrecl
    wtru
    @34
    @23
    cr
    wcel
    @24
    @40
    @39
    ad2ant2r
    @42
    @2
    @7
    vn
    @43
    @44
    fsumabs
    @42
    @21
    @22
    @2
    vn
    @42
    c1
    @20
    fzfid
    @42
    @36
    wa
    #
    @7
    @45
    @27
    @28
    @36
    @27
    @42
    @38
    adantl
    @29
    syl
    #
    abscld
    @45
    @7
    @46
    absge0d
    @42
    @20
    @1
    cuz
    cfv
    wcel
    #
    @2
    @21
    wss
    @42
    @24
    @32
    @0
    @19
    cle
    wbr
    @47
    wtru
    @24
    @41
    simplr
    #
    @25
    @32
    @33
    @40
    simprll
    #
    @42
    @0
    @19
    @48
    @49
    @25
    @34
    @40
    simprr
    ltled
    @0
    @19
    flword2
    syl3anc
    @1
    c1
    @20
    fzss2
    syl
    fsumless
    letrd
    o1bddrp
    trud
    @12
    @18
    vc
    crp
    @11
    @17
    vm
    cr
    cz
    @0
    cz
    wcel
    #
    @11
    @17
    @24
    @11
    wi
    @50
    @24
    @11
    @0
    zre
    imim1i
    @50
    @9
    @16
    @10
    cle
    @50
    @8
    @15
    cabs
    @50
    @2
    @14
    @7
    vn
    @50
    @1
    @0
    c1
    cfz
    @0
    flid
    oveq2d
    sumeq1d
    fveq2d
    breq1d
    mpbidi
    ralimi2
    reximi
    ax-mp
end
