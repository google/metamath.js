include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "c2.mm"
include "c7.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "c9.mm"
include "c5.mm"
include "cdp2.mm"
include "cdp.mm"
include "cn.mm"
include "wral.mm"
include "c4.mm"
include "c8.mm"
include "cmul.mm"
include "cioo.mm"
include "cvma.mm"
include "cof.mm"
include "cvts.mm"
include "ci.mm"
include "cpi.mm"
include "cneg.mm"
include "ce.mm"
include "citg.mm"
include "w3a.mm"
include "cpnf.mm"
include "cico.mm"
include "cmap.mm"
include "wrex.mm"
include "wi.mm"
include "cdvds.mm"
include "wn.mm"
include "cz.mm"
include "crab.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "wcel.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "negeq.mm"
include "fveq2d.mm"
include "adantr.mm"
include "itgeq2dv.mm"
include "breq12d.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ax-hgt749.mm"
include "a1i.mm"
include "syl6eleq.mm"
include "rspcdva.mm"
include "mpd.mm"

theorem hgt749d
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let cO: class O
  let vn: setvar n
  assume hgt749d.o: |- O = { z e. ZZ | -. 2 || z }
  assume hgt749d.n: |- ( ph -> N e. O )
  assume hgt749d.1: |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N )

  disjoint N h
  disjoint N k
  disjoint N x
  disjoint h k
  disjoint h x
  disjoint k x
  disjoint h m
  disjoint h z
  disjoint k m
  disjoint k z
  disjoint m x
  disjoint m z
  disjoint x z
  disjoint N n
  disjoint h n
  disjoint k n
  disjoint n x
  disjoint m n
  disjoint n z
  disjoint n ph
  assert |- ( ph -> E. h e. ( ( 0 [,) +oo ) ^m NN ) E. k e. ( ( 0 [,) +oo ) ^m NN ) ( A. m e. NN ( k ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 ) /\ A. m e. NN ( h ` m ) <_ ( 1 . _ 4 _ 1 4 ) /\ ( ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) x. ( N ^ 2 ) ) <_ S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. h ) vts N ) ` x ) x. ( ( ( ( Lam oF x. k ) vts N ) ` x ) ^ 2 ) ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x ) )

  proof
    wph
    c1
    cc0
    cdc
    c2
    c7
    cdc
    cexp
    co
    #
    cN
    cle
    wbr
    #
    vm
    cv
    #
    vk
    cv
    #
    cfv
    c1
    cc0
    c7
    c9
    c9
    c5
    c5
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp
    co
    cle
    wbr
    vm
    cn
    wral
    #
    @2
    vh
    cv
    #
    cfv
    c1
    c4
    c1
    c4
    cdp2
    cdp2
    cdp
    co
    cle
    wbr
    vm
    cn
    wral
    #
    cc0
    cc0
    cc0
    cc0
    c4
    c2
    c2
    c4
    c8
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp
    co
    #
    cN
    c2
    cexp
    co
    #
    cmul
    co
    #
    vx
    cc0
    c1
    cioo
    co
    #
    vx
    cv
    #
    cvma
    @5
    cmul
    cof
    #
    co
    #
    cN
    cvts
    co
    #
    cfv
    #
    @11
    cvma
    @3
    @12
    co
    #
    cN
    cvts
    co
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    #
    cN
    cneg
    #
    @11
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    citg
    #
    cle
    wbr
    #
    w3a
    #
    vk
    cc0
    cpnf
    cico
    co
    cn
    cmap
    co
    #
    wrex
    #
    vh
    @30
    wrex
    #
    hgt749d.1
    wph
    @0
    vn
    cv
    #
    cle
    wbr
    #
    @4
    @6
    @7
    @33
    c2
    cexp
    co
    #
    cmul
    co
    #
    vx
    @10
    @11
    @13
    @33
    cvts
    co
    #
    cfv
    #
    @11
    @16
    @33
    cvts
    co
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    @21
    @33
    cneg
    #
    @11
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    citg
    #
    cle
    wbr
    #
    w3a
    #
    vk
    @30
    wrex
    #
    vh
    @30
    wrex
    #
    wi
    #
    @1
    @32
    wi
    vn
    c2
    vz
    cv
    cdvds
    wbr
    wn
    vz
    cz
    crab
    #
    cN
    @33
    cN
    wceq
    #
    @34
    @1
    @52
    @32
    @33
    cN
    @0
    cle
    breq2
    @55
    @51
    @31
    vh
    @30
    @55
    @50
    @29
    vk
    @30
    @55
    @49
    @28
    @4
    @6
    @55
    @36
    @9
    @48
    @27
    cle
    @55
    @35
    @8
    @7
    cmul
    @33
    cN
    c2
    cexp
    oveq1
    oveq2d
    @55
    vx
    @10
    @47
    @26
    @55
    @47
    @26
    wceq
    @11
    @10
    wcel
    @55
    @42
    @20
    @46
    @25
    cmul
    @55
    @38
    @15
    @41
    @19
    cmul
    @55
    @11
    @37
    @14
    @33
    cN
    @13
    cvts
    oveq2
    fveq1d
    @55
    @40
    @18
    c2
    cexp
    @55
    @11
    @39
    @17
    @33
    cN
    @16
    cvts
    oveq2
    fveq1d
    oveq1d
    oveq12d
    @55
    @45
    @24
    ce
    @55
    @44
    @23
    @21
    cmul
    @55
    @43
    @22
    @11
    cmul
    @33
    cN
    negeq
    oveq1d
    oveq2d
    fveq2d
    oveq12d
    adantr
    itgeq2dv
    breq12d
    3anbi3d
    rexbidv
    rexbidv
    imbi12d
    @53
    vn
    @54
    wral
    wph
    vx
    vz
    vh
    vk
    vm
    vn
    ax-hgt749
    a1i
    wph
    cN
    cO
    @54
    hgt749d.n
    hgt749d.o
    syl6eleq
    rspcdva
    mpd
end
