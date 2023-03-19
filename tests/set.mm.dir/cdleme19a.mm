include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp23.mm"
include "simp33.mm"
include "hlatlej1.mm"
include "wa.mm"
include "wb.mm"
include "atbase.mm"
include "syl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "hlatlej2.mm"
include "clc.mm"
include "wne.mm"
include "wi.mm"
include "hlcvl.mm"
include "simp31.mm"
include "simp32.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "cvlatexch1.mm"
include "syl131anc.mm"
include "mpd.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "breqtrrd.mm"
include "latasymd.mm"
include "oveq1d.mm"
include "syl5eq.mm"

theorem cdleme19a
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )


  assert |- ( ( K e. HL /\ ( R e. A /\ S e. A /\ T e. A ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ R .<_ ( S .\/ T ) ) ) -> D = ( ( S .\/ T ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    w3a
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
    cS
    @5
    c.le
    wbr
    wn
    #
    cR
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cD
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    @8
    cW
    c.an
    co
    cdleme19.d
    @11
    @12
    @8
    cW
    c.an
    @11
    cK
    cbs
    cfv
    #
    cK
    c.le
    @12
    @8
    @13
    eqid
    #
    cdleme19.l
    @0
    @4
    cK
    clat
    wcel
    #
    @10
    cK
    hllat
    3ad2ant1
    #
    @11
    @0
    @1
    @2
    @12
    @13
    wcel
    #
    @0
    @4
    @10
    simp1
    #
    @0
    @1
    @2
    @3
    @10
    simp21
    #
    @0
    @1
    @2
    @3
    @10
    simp22
    #
    cA
    @13
    c.or
    cK
    cR
    cS
    @14
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    #
    @11
    @0
    @2
    @3
    @8
    @13
    wcel
    #
    @18
    @20
    @0
    @1
    @2
    @3
    @10
    simp23
    #
    cA
    @13
    c.or
    cK
    cS
    cT
    @14
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    #
    @11
    @9
    cS
    @8
    c.le
    wbr
    #
    @12
    @8
    c.le
    wbr
    #
    @0
    @4
    @6
    @7
    @9
    simp33
    #
    @11
    @0
    @2
    @3
    @25
    @18
    @20
    @23
    cA
    cS
    cT
    c.or
    cK
    c.le
    cdleme19.l
    cdleme19.j
    cdleme19.a
    hlatlej1
    syl3anc
    @11
    @15
    cR
    @13
    wcel
    #
    cS
    @13
    wcel
    #
    @22
    @9
    @25
    wa
    @26
    wb
    @16
    @11
    @1
    @28
    @19
    cA
    @13
    cR
    cK
    @14
    cdleme19.a
    atbase
    syl
    @11
    @2
    @29
    @20
    cA
    @13
    cS
    cK
    @14
    cdleme19.a
    atbase
    syl
    #
    @24
    @13
    c.or
    cK
    c.le
    cR
    cS
    @8
    @14
    cdleme19.l
    cdleme19.j
    latjle12
    syl13anc
    mpbi2and
    @11
    cS
    @12
    c.le
    wbr
    #
    cT
    @12
    c.le
    wbr
    #
    @8
    @12
    c.le
    wbr
    #
    @11
    @0
    @1
    @2
    @31
    @18
    @19
    @20
    cA
    cR
    cS
    c.or
    cK
    c.le
    cdleme19.l
    cdleme19.j
    cdleme19.a
    hlatlej2
    syl3anc
    @11
    cT
    cS
    cR
    c.or
    co
    #
    @12
    c.le
    @11
    @9
    cT
    @34
    c.le
    wbr
    #
    @27
    @11
    cK
    clc
    wcel
    #
    @1
    @3
    @2
    cR
    cS
    wne
    #
    @9
    @35
    wi
    @0
    @4
    @36
    @10
    cK
    hlcvl
    3ad2ant1
    @19
    @23
    @20
    @11
    @6
    @7
    @37
    @0
    @4
    @6
    @7
    @9
    simp31
    @0
    @4
    @6
    @7
    @9
    simp32
    cR
    cS
    @5
    c.le
    nbrne2
    syl2anc
    cA
    cR
    cT
    cS
    c.or
    cK
    c.le
    cdleme19.l
    cdleme19.j
    cdleme19.a
    cvlatexch1
    syl131anc
    mpd
    @11
    @0
    @1
    @2
    @12
    @34
    wceq
    @18
    @19
    @20
    cA
    c.or
    cK
    cR
    cS
    cdleme19.j
    cdleme19.a
    hlatjcom
    syl3anc
    breqtrrd
    @11
    @15
    @29
    cT
    @13
    wcel
    #
    @17
    @31
    @32
    wa
    @33
    wb
    @16
    @30
    @11
    @3
    @38
    @23
    cA
    @13
    cT
    cK
    @14
    cdleme19.a
    atbase
    syl
    @21
    @13
    c.or
    cK
    c.le
    cS
    cT
    @12
    @14
    cdleme19.l
    cdleme19.j
    latjle12
    syl13anc
    mpbi2and
    latasymd
    oveq1d
    syl5eq
end
