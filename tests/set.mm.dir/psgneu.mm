include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "cid.mm"
include "cdif.mm"
include "cfn.mm"
include "eqid.mm"
include "psgneldm.mm"
include "simplbi.mm"
include "csymg.mm"
include "elbasfv.mm"
include "syl.mm"
include "psgneldm2.mm"
include "ibi.mm"
include "simpr.mm"
include "ovex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "spcev.mm"
include "sylancl.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexcom4.mm"
include "sylib.mm"
include "reeanv.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "eqtr3d.mm"
include "psgnuni.mm"
include "simprlr.mm"
include "simprrr.mm"
include "3eqtr4d.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "alrimivv.mm"
include "rexbidv.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem psgneu
  let vw: setvar w
  let cD: class D
  let cP: class P
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vp: setvar p
  let cV: class V
  let cW: class W
  assume psgnval.g: |- G = ( SymGrp ` D )
  assume psgnval.t: |- T = ran ( pmTrsp ` D )
  assume psgnval.n: |- N = ( pmSgn ` D )

  disjoint s w
  disjoint G s
  disjoint G w
  disjoint N s
  disjoint N w
  disjoint P s
  disjoint P w
  disjoint T s
  disjoint T w
  disjoint D s
  disjoint D w
  disjoint s t
  disjoint s x
  disjoint t w
  disjoint t x
  disjoint G t
  disjoint w x
  disjoint G x
  disjoint N t
  disjoint N x
  disjoint P t
  disjoint P x
  disjoint T t
  disjoint T x
  disjoint p s
  disjoint p t
  disjoint D t
  disjoint p w
  disjoint D p
  disjoint G p
  disjoint T p
  disjoint V s
  disjoint V p
  disjoint W s
  disjoint W w
  assert |- ( P e. dom N -> E! s E. w e. Word T ( P = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) )

  proof
    cP
    cN
    cdm
    wcel
    #
    cP
    cG
    vw
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vs
    cv
    #
    c1
    cneg
    #
    @1
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    vw
    cT
    cword
    #
    wrex
    #
    vs
    wex
    #
    @11
    cP
    cG
    vx
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vt
    cv
    #
    @5
    @13
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    vx
    @10
    wrex
    #
    wa
    #
    @4
    @16
    wceq
    #
    wi
    #
    vt
    wal
    vs
    wal
    @11
    vs
    weu
    @0
    @9
    vs
    wex
    #
    vw
    @10
    wrex
    #
    @12
    @0
    @3
    vw
    @10
    wrex
    #
    @26
    @0
    @27
    @0
    cD
    cvv
    wcel
    #
    @0
    @27
    wb
    @0
    cP
    cG
    cbs
    cfv
    #
    wcel
    #
    @28
    @0
    @30
    cP
    cid
    cdif
    cdm
    cfn
    wcel
    @29
    cD
    cP
    cG
    cN
    psgnval.g
    psgnval.n
    @29
    eqid
    #
    psgneldm
    simplbi
    @29
    cG
    csymg
    cP
    cD
    psgnval.g
    @31
    elbasfv
    syl
    #
    vw
    cD
    cP
    cT
    cG
    cN
    cvv
    psgnval.g
    psgnval.t
    psgnval.n
    psgneldm2
    syl
    ibi
    @0
    @3
    @25
    vw
    @10
    @0
    @1
    @10
    wcel
    #
    wa
    #
    @3
    @25
    @34
    @3
    wa
    @3
    @7
    @7
    wceq
    #
    @25
    @34
    @3
    simpr
    @7
    eqid
    @9
    @3
    @35
    wa
    vs
    @7
    @5
    @6
    cexp
    ovex
    @8
    @8
    @35
    @3
    @4
    @7
    @7
    eqeq1
    anbi2d
    spcev
    sylancl
    ex
    reximdva
    mpd
    @9
    vw
    vs
    @10
    rexcom4
    sylib
    @0
    @24
    vs
    vt
    @22
    @9
    @20
    wa
    #
    vx
    @10
    wrex
    vw
    @10
    wrex
    @0
    @23
    @9
    @20
    vw
    vx
    @10
    @10
    reeanv
    @0
    @36
    @23
    vw
    vx
    @10
    @10
    @0
    @33
    @13
    @10
    wcel
    #
    wa
    #
    wa
    #
    @36
    @23
    @39
    @36
    wa
    #
    @7
    @18
    @4
    @16
    @40
    cD
    cT
    cG
    cvv
    @1
    @13
    psgnval.g
    psgnval.t
    @0
    @28
    @38
    @36
    @32
    ad2antrr
    @0
    @33
    @37
    @36
    simplrl
    @0
    @33
    @37
    @36
    simplrr
    @40
    cP
    @2
    @14
    @39
    @3
    @8
    @20
    simprll
    @39
    @9
    @15
    @19
    simprrl
    eqtr3d
    psgnuni
    @39
    @3
    @8
    @20
    simprlr
    @39
    @9
    @15
    @19
    simprrr
    3eqtr4d
    ex
    rexlimdvva
    syl5bir
    alrimivv
    @11
    @21
    vs
    vt
    @23
    @11
    @3
    @16
    @7
    wceq
    #
    wa
    #
    vw
    @10
    wrex
    @21
    @23
    @9
    @42
    vw
    @10
    @23
    @8
    @41
    @3
    @4
    @16
    @7
    eqeq1
    anbi2d
    rexbidv
    @42
    @20
    vw
    vx
    @10
    @1
    @13
    wceq
    #
    @3
    @15
    @41
    @19
    @43
    @2
    @14
    cP
    @1
    @13
    cG
    cgsu
    oveq2
    eqeq2d
    @43
    @7
    @18
    @16
    @43
    @6
    @17
    @5
    cexp
    @1
    @13
    chash
    fveq2
    oveq2d
    eqeq2d
    anbi12d
    cbvrexv
    syl6bb
    eu4
    sylanbrc
end
