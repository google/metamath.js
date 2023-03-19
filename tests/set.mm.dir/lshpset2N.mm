include "clvec.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "lshpkrex.mm"
include "eleq1.mm"
include "biimparc.mm"
include "adantll.mm"
include "adantlr.mm"
include "simplll.mm"
include "simplr.mm"
include "lkrshp3.mm"
include "mpbid.mm"
include "ex.mm"
include "wi.mm"
include "eqimss2.mm"
include "eqimss.mm"
include "eqssd.mm"
include "a1i.mm"
include "jcad.mm"
include "reximdva.mm"
include "mpd.mm"
include "clss.mm"
include "cun.mm"
include "clspn.mm"
include "w3a.mm"
include "lkrshp.mm"
include "3adant3r.mm"
include "wb.mm"
include "eqid.mm"
include "islshp.mm"
include "3ad2ant1.mm"
include "neeq1.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "rexlimdv3a.mm"
include "sylibrd.mm"
include "impbid.mm"
include "abbi2dv.mm"

theorem lshpset2N
  let cD: class D
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vv: setvar v
  assume lshpset2.v: |- V = ( Base ` W )
  assume lshpset2.d: |- D = ( Scalar ` W )
  assume lshpset2.z: |- .0. = ( 0g ` D )
  assume lshpset2.h: |- H = ( LSHyp ` W )
  assume lshpset2.f: |- F = ( LFnl ` W )
  assume lshpset2.k: |- K = ( LKer ` W )

  disjoint F g
  disjoint g s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint V g
  disjoint W g
  disjoint W s
  disjoint g v
  disjoint K v
  disjoint V v
  disjoint s v
  disjoint W v
  assert |- ( W e. LVec -> H = { s | E. g e. F ( g =/= ( V X. { .0. } ) /\ s = ( K ` g ) ) } )

  proof
    cW
    clvec
    wcel
    #
    vg
    cv
    #
    cV
    c.0
    csn
    cxp
    wne
    #
    vs
    cv
    #
    @1
    cK
    cfv
    #
    wceq
    #
    wa
    #
    vg
    cF
    wrex
    #
    vs
    cH
    @0
    @3
    cH
    wcel
    #
    @7
    @0
    @8
    @7
    @0
    @8
    wa
    #
    @4
    @3
    wceq
    #
    vg
    cF
    wrex
    @7
    @3
    vg
    cF
    cH
    cK
    cW
    lshpset2.h
    lshpset2.f
    lshpset2.k
    lshpkrex
    @9
    @10
    @6
    vg
    cF
    @9
    @1
    cF
    wcel
    #
    wa
    #
    @10
    @2
    @5
    @12
    @10
    @2
    @12
    @10
    wa
    #
    @4
    cH
    wcel
    #
    @2
    @9
    @10
    @14
    @11
    @8
    @10
    @14
    @0
    @10
    @14
    @8
    @4
    @3
    cH
    eleq1
    biimparc
    adantll
    adantlr
    @13
    cD
    cF
    @1
    cH
    cK
    cV
    cW
    c.0
    lshpset2.v
    lshpset2.d
    lshpset2.z
    lshpset2.h
    lshpset2.f
    lshpset2.k
    @0
    @8
    @11
    @10
    simplll
    @9
    @11
    @10
    simplr
    lkrshp3
    mpbid
    ex
    @10
    @5
    wi
    @12
    @10
    @3
    @4
    @3
    @4
    eqimss2
    @4
    @3
    eqimss
    eqssd
    a1i
    jcad
    reximdva
    mpd
    ex
    @0
    @7
    @3
    cW
    clss
    cfv
    #
    wcel
    #
    @3
    cV
    wne
    #
    @3
    vv
    cv
    csn
    #
    cun
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    w3a
    #
    @8
    @0
    @6
    @24
    vg
    cF
    @0
    @11
    @6
    w3a
    #
    @24
    @4
    @15
    wcel
    #
    @4
    cV
    wne
    #
    @4
    @18
    cun
    #
    @20
    cfv
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    w3a
    #
    @25
    @14
    @32
    @0
    @11
    @2
    @14
    @5
    cD
    cF
    @1
    cH
    cK
    cV
    cW
    c.0
    lshpset2.v
    lshpset2.d
    lshpset2.z
    lshpset2.h
    lshpset2.f
    lshpset2.k
    lkrshp
    3adant3r
    @0
    @11
    @14
    @32
    wb
    @6
    vv
    @15
    @4
    cH
    @20
    cV
    cW
    clvec
    lshpset2.v
    @20
    eqid
    #
    @15
    eqid
    #
    lshpset2.h
    islshp
    3ad2ant1
    mpbid
    @6
    @0
    @24
    @32
    wb
    #
    @11
    @5
    @35
    @2
    @5
    @16
    @26
    @17
    @27
    @23
    @31
    @3
    @4
    @15
    eleq1
    @3
    @4
    cV
    neeq1
    @5
    @22
    @30
    vv
    cV
    @5
    @21
    @29
    cV
    @5
    @19
    @28
    @20
    @3
    @4
    @18
    uneq1
    fveq2d
    eqeq1d
    rexbidv
    3anbi123d
    adantl
    3ad2ant3
    mpbird
    rexlimdv3a
    vv
    @15
    @3
    cH
    @20
    cV
    cW
    clvec
    lshpset2.v
    @33
    @34
    lshpset2.h
    islshp
    sylibrd
    impbid
    abbi2dv
end
