include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "simprl.mm"
include "wceq.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wrex.mm"
include "simp11.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "eqid.mm"
include "llnbase.mm"
include "simp13.mm"
include "lplnbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "simp3.mm"
include "llnle.mm"
include "syl22anc.mm"
include "adantr.mm"
include "latmle1.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "lattrd.mm"
include "wb.mm"
include "simpl11.mm"
include "simpl12.mm"
include "llncmp.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "latasymd.mm"
include "rexlimddv.mm"
include "latleeqm1.mm"
include "mpbird.mm"
include "3expia.mm"
include "mt3d.mm"

theorem llnmlplnN
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vu: setvar u
  assume llnmlpln.l: |- .<_ = ( le ` K )
  assume llnmlpln.m: |- ./\ = ( meet ` K )
  assume llnmlpln.z: |- .0. = ( 0. ` K )
  assume llnmlpln.a: |- A = ( Atoms ` K )
  assume llnmlpln.n: |- N = ( LLines ` K )
  assume llnmlpln.p: |- P = ( LPlanes ` K )


  assert |- ( ( ( K e. HL /\ X e. N /\ Y e. P ) /\ ( -. X .<_ Y /\ ( X ./\ Y ) =/= .0. ) ) -> ( X ./\ Y ) e. A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cP
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    wn
    #
    cX
    cY
    c.an
    co
    #
    c.0
    wne
    #
    wa
    #
    wa
    @6
    cA
    wcel
    #
    @4
    @3
    @5
    @7
    simprl
    @3
    @8
    @9
    wn
    #
    @4
    @3
    @8
    @10
    w3a
    #
    @4
    @6
    cX
    wceq
    #
    @11
    vu
    cv
    #
    @6
    c.le
    wbr
    #
    @12
    vu
    cN
    @11
    @0
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @10
    @14
    vu
    cN
    wrex
    @0
    @1
    @2
    @8
    @10
    simp11
    #
    @11
    cK
    clat
    wcel
    #
    cX
    @15
    wcel
    #
    cY
    @15
    wcel
    #
    @16
    @11
    @0
    @18
    @17
    cK
    hllat
    syl
    #
    @11
    @1
    @19
    @0
    @1
    @2
    @8
    @10
    simp12
    @15
    cK
    cN
    cX
    @15
    eqid
    #
    llnmlpln.n
    llnbase
    syl
    #
    @11
    @2
    @20
    @0
    @1
    @2
    @8
    @10
    simp13
    @15
    cP
    cK
    cY
    @22
    llnmlpln.p
    lplnbase
    syl
    #
    @15
    cK
    c.an
    cX
    cY
    @22
    llnmlpln.m
    latmcl
    syl3anc
    #
    @3
    @5
    @7
    @10
    simp2r
    @3
    @8
    @10
    simp3
    vu
    cA
    @15
    cK
    c.le
    cN
    @6
    c.0
    @22
    llnmlpln.l
    llnmlpln.z
    llnmlpln.a
    llnmlpln.n
    llnle
    syl22anc
    @11
    @13
    cN
    wcel
    #
    @14
    wa
    #
    wa
    #
    @15
    cK
    c.le
    @6
    cX
    @22
    llnmlpln.l
    @11
    @18
    @27
    @21
    adantr
    #
    @11
    @16
    @27
    @25
    adantr
    #
    @11
    @19
    @27
    @23
    adantr
    #
    @11
    @6
    cX
    c.le
    wbr
    #
    @27
    @11
    @18
    @19
    @20
    @32
    @21
    @23
    @24
    @15
    cK
    c.le
    c.an
    cX
    cY
    @22
    llnmlpln.l
    llnmlpln.m
    latmle1
    syl3anc
    adantr
    #
    @28
    @13
    cX
    @6
    c.le
    @28
    @13
    cX
    c.le
    wbr
    #
    @13
    cX
    wceq
    #
    @28
    @15
    cK
    c.le
    @13
    @6
    cX
    @22
    llnmlpln.l
    @29
    @26
    @13
    @15
    wcel
    @11
    @14
    @15
    cK
    cN
    @13
    @22
    llnmlpln.n
    llnbase
    ad2antrl
    @30
    @31
    @11
    @26
    @14
    simprr
    #
    @33
    lattrd
    @28
    @0
    @26
    @1
    @34
    @35
    wb
    @0
    @1
    @2
    @8
    @10
    @27
    simpl11
    @11
    @26
    @14
    simprl
    @0
    @1
    @2
    @8
    @10
    @27
    simpl12
    cK
    c.le
    cN
    @13
    cX
    llnmlpln.l
    llnmlpln.n
    llncmp
    syl3anc
    mpbid
    @36
    eqbrtrrd
    latasymd
    rexlimddv
    @11
    @18
    @19
    @20
    @4
    @12
    wb
    @21
    @23
    @24
    @15
    cK
    c.le
    c.an
    cX
    cY
    @22
    llnmlpln.l
    llnmlpln.m
    latleeqm1
    syl3anc
    mpbird
    3expia
    mt3d
end
