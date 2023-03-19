include "cfv.mm"
include "cioo.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "climc.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cv.mm"
include "cmul.mm"
include "csin.mm"
include "cmpt.mm"
include "cpi.mm"
include "ccos.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "cc0.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "dirkercncflem1.mm"
include "simprd.mm"
include "r19.26.mm"
include "sylib.mm"
include "simpld.mm"
include "r19.21bi.mm"
include "eqid.mm"
include "dirkercncflem2.mm"
include "cr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cun.mm"
include "crest.mm"
include "cc.mm"
include "cn.mm"
include "wf.mm"
include "dirkerf.mm"
include "syl.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "ioossre.mm"
include "ssdifssd.mm"
include "cnt.mm"
include "crn.mm"
include "ctg.mm"
include "iooretop.mm"
include "ctop.mm"
include "wb.mm"
include "retop.mm"
include "uniretop.mm"
include "isopn3.mm"
include "sylancr.mm"
include "mpbii.mm"
include "eleqtrrd.mm"
include "tgioo2.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "snssd.mm"
include "ssequn2.mm"
include "uncom.mm"
include "undif.mm"
include "syl5eq.mm"
include "fveq12d.mm"
include "limcres.mm"

theorem dirkercncflem3
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume dirkercncflem3.d: |- D = ( n e. NN |-> ( y e. RR |-> if ( ( y mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. y ) ) / ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) ) ) ) )
  assume dirkercncflem3.a: |- A = ( Y - _pi )
  assume dirkercncflem3.b: |- B = ( Y + _pi )
  assume dirkercncflem3.f: |- F = ( y e. ( A (,) B ) |-> ( ( sin ` ( ( n + ( 1 / 2 ) ) x. y ) ) / ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) ) )
  assume dirkercncflem3.g: |- G = ( y e. ( A (,) B ) |-> ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) )
  assume dirkercncflem3.n: |- ( ph -> N e. NN )
  assume dirkercncflem3.yr: |- ( ph -> Y e. RR )
  assume dirkercncflem3.yod: |- ( ph -> ( Y mod ( 2 x. _pi ) ) = 0 )

  disjoint A y
  disjoint B y
  disjoint D y
  disjoint N y
  disjoint Y y
  disjoint n y
  disjoint ph y
  disjoint A w
  disjoint A z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint B w
  disjoint B z
  disjoint N w
  disjoint N z
  disjoint Y w
  disjoint Y z
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( ( D ` N ) ` Y ) e. ( ( D ` N ) limCC Y ) )

  proof
    wph
    cY
    cN
    cD
    cfv
    #
    cfv
    @0
    cA
    cB
    cioo
    co
    #
    cY
    csn
    #
    cdif
    #
    cres
    cY
    climc
    co
    @0
    cY
    climc
    co
    wph
    vy
    vz
    cA
    cB
    cD
    vn
    vw
    @3
    cN
    c1
    c2
    cdiv
    co
    caddc
    co
    #
    vw
    cv
    #
    cmul
    co
    #
    csin
    cfv
    #
    cmpt
    vw
    @3
    c2
    cpi
    cmul
    co
    #
    @5
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmpt
    vw
    @3
    @4
    @6
    ccos
    cfv
    #
    cmul
    co
    #
    cmpt
    vw
    @3
    cpi
    @9
    ccos
    cfv
    #
    cmul
    co
    #
    cmpt
    vz
    @1
    @4
    @4
    vz
    cv
    #
    cmul
    co
    ccos
    cfv
    cmul
    co
    cpi
    @16
    c2
    cdiv
    co
    ccos
    cfv
    cmul
    co
    cdiv
    co
    cmpt
    #
    cN
    cY
    dirkercncflem3.d
    vw
    vy
    @3
    @7
    @4
    vy
    cv
    #
    cmul
    co
    #
    csin
    cfv
    @5
    @18
    wceq
    #
    @6
    @19
    csin
    @5
    @18
    @4
    cmul
    oveq2
    #
    fveq2d
    cbvmptv
    vw
    vy
    @3
    @11
    @8
    @18
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    @20
    @10
    @23
    @8
    cmul
    @20
    @9
    @22
    csin
    @5
    @18
    c2
    cdiv
    oveq1
    #
    fveq2d
    oveq2d
    cbvmptv
    wph
    @23
    cc0
    wne
    #
    vy
    @3
    wph
    @25
    vy
    @3
    wral
    #
    @22
    ccos
    cfv
    #
    cc0
    wne
    #
    vy
    @3
    wral
    #
    wph
    @25
    @28
    wa
    vy
    @3
    wral
    #
    @26
    @29
    wa
    wph
    cY
    @1
    wcel
    #
    @30
    wph
    vy
    cA
    cB
    cY
    dirkercncflem3.a
    dirkercncflem3.b
    dirkercncflem3.yr
    dirkercncflem3.yod
    dirkercncflem1
    #
    simprd
    @25
    @28
    vy
    @3
    r19.26
    sylib
    #
    simpld
    r19.21bi
    vw
    vy
    @3
    @13
    @4
    @19
    ccos
    cfv
    #
    cmul
    co
    @20
    @12
    @34
    @4
    cmul
    @20
    @6
    @19
    ccos
    @21
    fveq2d
    oveq2d
    cbvmptv
    vw
    vy
    @3
    @15
    cpi
    @27
    cmul
    co
    @20
    @14
    @27
    cpi
    cmul
    @20
    @9
    @22
    ccos
    @24
    fveq2d
    oveq2d
    cbvmptv
    @17
    eqid
    dirkercncflem3.n
    wph
    @31
    @30
    @32
    simpld
    #
    dirkercncflem3.yod
    wph
    @28
    vy
    @3
    wph
    @26
    @29
    @33
    simprd
    r19.21bi
    dirkercncflem2
    wph
    cr
    cY
    @3
    @0
    ccnfld
    ctopn
    cfv
    #
    cr
    @2
    cun
    #
    crest
    co
    #
    @36
    wph
    cr
    cr
    cc
    @0
    wph
    cN
    cn
    wcel
    cr
    cr
    @0
    wf
    dirkercncflem3.n
    vy
    cD
    vn
    cN
    dirkercncflem3.d
    dirkerf
    syl
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    fssd
    wph
    @1
    cr
    @2
    @1
    cr
    wss
    #
    wph
    cA
    cB
    ioossre
    a1i
    #
    ssdifssd
    @39
    @36
    eqid
    #
    @38
    eqid
    wph
    cY
    @1
    @36
    cr
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @3
    @2
    cun
    #
    @38
    cnt
    cfv
    #
    cfv
    wph
    cY
    @1
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    #
    cfv
    #
    @45
    wph
    cY
    @1
    @50
    @35
    wph
    @1
    @48
    wcel
    #
    @50
    @1
    wceq
    #
    cA
    cB
    iooretop
    wph
    @48
    ctop
    wcel
    @40
    @51
    @52
    wb
    retop
    @41
    @1
    @48
    cr
    uniretop
    isopn3
    sylancr
    mpbii
    eleqtrrd
    wph
    @1
    @49
    @44
    wph
    @48
    @43
    cnt
    @48
    @43
    wceq
    wph
    @36
    @42
    tgioo2
    a1i
    fveq2d
    fveq1d
    eleqtrd
    wph
    @46
    @1
    @47
    @44
    wph
    @38
    @43
    cnt
    wph
    @37
    cr
    @36
    crest
    wph
    @2
    cr
    wss
    @37
    cr
    wceq
    wph
    cY
    cr
    dirkercncflem3.yr
    snssd
    @2
    cr
    ssequn2
    sylib
    oveq2d
    fveq2d
    wph
    @46
    @2
    @3
    cun
    #
    @1
    @3
    @2
    uncom
    wph
    @2
    @1
    wss
    @53
    @1
    wceq
    wph
    cY
    @1
    @35
    snssd
    @2
    @1
    undif
    sylib
    syl5eq
    fveq12d
    eleqtrrd
    limcres
    eleqtrd
end
