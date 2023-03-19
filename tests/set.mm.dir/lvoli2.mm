include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3.mm"
include "eqidd.mm"
include "neeq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "notbid.mm"
include "oveq1d.mm"
include "3anbi123d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "3exp.mm"
include "wi.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "breq1.mm"
include "3anbi23d.mm"
include "3anbi3d.mm"
include "syl3anc.mm"
include "ex.mm"
include "reximdv.mm"
include "syldd.mm"
include "3imp.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp11.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp2r.mm"
include "islvol5.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lvoli2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume lvoli2.l: |- .<_ = ( le ` K )
  assume lvoli2.j: |- .\/ = ( join ` K )
  assume lvoli2.a: |- A = ( Atoms ` K )
  assume lvoli2.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( ( ( P .\/ Q ) .\/ R ) .\/ S ) e. V )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cS
    @8
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    @11
    cS
    c.or
    co
    #
    cV
    wcel
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    vr
    cv
    #
    @18
    @19
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    vs
    cv
    #
    @22
    @21
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @16
    @26
    @25
    c.or
    co
    #
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    @3
    @6
    @14
    @35
    @3
    @6
    @14
    @20
    cR
    @22
    c.le
    wbr
    #
    wn
    #
    cS
    @22
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @16
    @38
    cS
    c.or
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    @35
    @3
    @6
    @14
    @46
    @15
    @1
    @2
    @14
    @16
    @16
    wceq
    #
    @46
    @0
    @1
    @2
    @6
    @14
    simp12
    @0
    @1
    @2
    @6
    @14
    simp13
    @3
    @6
    @14
    simp3
    @15
    @16
    eqidd
    @44
    @14
    @47
    wa
    cP
    @19
    wne
    #
    cR
    cP
    @19
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cS
    @49
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @16
    @52
    cS
    c.or
    co
    #
    wceq
    #
    wa
    vp
    vq
    cP
    cQ
    cA
    cA
    @18
    cP
    wceq
    #
    @41
    @55
    @43
    @57
    @58
    @20
    @48
    @37
    @51
    @40
    @54
    @18
    cP
    @19
    neeq1
    @58
    @36
    @50
    @58
    @22
    @49
    cR
    c.le
    @18
    cP
    @19
    c.or
    oveq1
    #
    breq2d
    notbid
    @58
    @39
    @53
    @58
    @38
    @52
    cS
    c.le
    @58
    @22
    @49
    cR
    c.or
    @59
    oveq1d
    #
    breq2d
    notbid
    3anbi123d
    @58
    @42
    @56
    @16
    @58
    @38
    @52
    cS
    c.or
    @60
    oveq1d
    eqeq2d
    anbi12d
    @19
    cQ
    wceq
    #
    @55
    @14
    @57
    @47
    @61
    @48
    @7
    @51
    @10
    @54
    @13
    @19
    cQ
    cP
    neeq2
    @61
    @50
    @9
    @61
    @49
    @8
    cR
    c.le
    @19
    cQ
    cP
    c.or
    oveq2
    #
    breq2d
    notbid
    @61
    @53
    @12
    @61
    @52
    @11
    cS
    c.le
    @61
    @49
    @8
    cR
    c.or
    @62
    oveq1d
    #
    breq2d
    notbid
    3anbi123d
    @61
    @56
    @16
    @16
    @61
    @52
    @11
    cS
    c.or
    @63
    oveq1d
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    3exp
    @3
    @6
    @46
    @35
    wi
    @3
    @6
    wa
    #
    @45
    @34
    vp
    cA
    @64
    @44
    @33
    vq
    cA
    @64
    @44
    @33
    @64
    @44
    wa
    @4
    @5
    @44
    @33
    @3
    @4
    @5
    @44
    simplrl
    @3
    @4
    @5
    @44
    simplrr
    @64
    @44
    simpr
    @32
    @44
    @20
    @37
    @25
    @38
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @16
    @38
    @25
    c.or
    co
    #
    wceq
    #
    wa
    vr
    vs
    cR
    cS
    cA
    cA
    @21
    cR
    wceq
    #
    @29
    @67
    @31
    @69
    @70
    @24
    @37
    @28
    @66
    @20
    @70
    @23
    @36
    @21
    cR
    @22
    c.le
    breq1
    notbid
    @70
    @27
    @65
    @70
    @26
    @38
    @25
    c.le
    @21
    cR
    @22
    c.or
    oveq2
    #
    breq2d
    notbid
    3anbi23d
    @70
    @30
    @68
    @16
    @70
    @26
    @38
    @25
    c.or
    @71
    oveq1d
    eqeq2d
    anbi12d
    @25
    cS
    wceq
    #
    @67
    @41
    @69
    @43
    @72
    @66
    @40
    @20
    @37
    @72
    @65
    @39
    @25
    cS
    @38
    c.le
    breq1
    notbid
    3anbi3d
    @72
    @68
    @42
    @16
    @25
    cS
    @38
    c.or
    oveq2
    eqeq2d
    anbi12d
    rspc2ev
    syl3anc
    ex
    reximdv
    reximdv
    ex
    syldd
    3imp
    @15
    @0
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    @35
    wb
    @0
    @1
    @2
    @6
    @14
    simp11
    #
    @15
    cK
    clat
    wcel
    #
    @11
    @73
    wcel
    #
    cS
    @73
    wcel
    #
    @74
    @15
    @0
    @76
    @75
    cK
    hllat
    syl
    #
    @15
    @76
    @8
    @73
    wcel
    #
    cR
    @73
    wcel
    #
    @77
    @79
    @3
    @6
    @80
    @14
    cA
    @73
    c.or
    cK
    cP
    cQ
    @73
    eqid
    #
    lvoli2.j
    lvoli2.a
    hlatjcl
    3ad2ant1
    @15
    @4
    @81
    @3
    @4
    @5
    @14
    simp2l
    cA
    @73
    cR
    cK
    @82
    lvoli2.a
    atbase
    syl
    @73
    c.or
    cK
    @8
    cR
    @82
    lvoli2.j
    latjcl
    syl3anc
    @15
    @5
    @78
    @3
    @4
    @5
    @14
    simp2r
    cA
    @73
    cS
    cK
    @82
    lvoli2.a
    atbase
    syl
    @73
    c.or
    cK
    @11
    cS
    @82
    lvoli2.j
    latjcl
    syl3anc
    cA
    @73
    c.or
    cK
    c.le
    cV
    @16
    vs
    vr
    vq
    vp
    @82
    lvoli2.l
    lvoli2.j
    lvoli2.a
    lvoli2.v
    islvol5
    syl2anc
    mpbird
end
