include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wne.mm"
include "w3a.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp133.mm"
include "simp132.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp12.mm"
include "simp131.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle1.mm"
include "wceq.mm"
include "simp33.mm"
include "simp32.mm"
include "cdleme22d.mm"
include "syl131anc.mm"
include "simp32l.mm"
include "jca.mm"
include "cdleme16.mm"
include "syl332anc.mm"
include "eqtr2d.mm"
include "hlatjcom.mm"
include "3brtr3d.mm"
include "clc.mm"
include "wi.mm"
include "hlcvl.mm"
include "simp33l.mm"
include "simp33r.mm"
include "cdleme3.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "cvlatexch1.mm"
include "mpd.mm"

theorem cdleme22g
  let cA: class A
  let cP: class P
  let cQ: class Q
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
  let cV: class V
  let cW: class W
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )
  assume cdleme22g.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme22g.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme22g.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( T e. A /\ -. T .<_ W ) /\ ( -. T .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ P =/= Q ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( S =/= T /\ S .<_ ( T .\/ V ) ) /\ ( V e. A /\ V .<_ W ) ) ) -> F .<_ ( G .\/ V ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
    #
    cT
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    @4
    c.le
    wbr
    wn
    #
    cP
    cQ
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    cS
    cT
    wne
    #
    cS
    cT
    cV
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    w3a
    #
    cV
    cG
    cF
    c.or
    co
    #
    c.le
    wbr
    #
    cF
    cG
    cV
    c.or
    co
    c.le
    wbr
    #
    @21
    cF
    cG
    c.or
    co
    #
    cW
    c.an
    co
    #
    @25
    cV
    @22
    c.le
    @21
    cK
    clat
    wcel
    #
    @25
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @28
    wcel
    #
    @26
    @25
    c.le
    wbr
    @21
    @0
    @27
    @0
    @1
    @3
    @8
    @12
    @20
    simp11l
    #
    cK
    hllat
    syl
    @21
    @0
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    @29
    @31
    @21
    @2
    @10
    @11
    @13
    @7
    @6
    @32
    @2
    @3
    @8
    @12
    @20
    simp11
    #
    @9
    @10
    @11
    @20
    simp2l
    #
    @9
    @10
    @11
    @20
    simp2r
    #
    @9
    @12
    @13
    @16
    @19
    simp31
    #
    @5
    @6
    @7
    @2
    @3
    @12
    @20
    simp133
    #
    @5
    @6
    @7
    @2
    @3
    @12
    @20
    simp132
    #
    cA
    cP
    cQ
    cS
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22g.u
    cdleme22g.f
    cdleme3fa
    syl132anc
    #
    @21
    @2
    @10
    @11
    @3
    @7
    @5
    @33
    @34
    @35
    @36
    @2
    @3
    @8
    @12
    @20
    simp12
    #
    @38
    @5
    @6
    @7
    @2
    @3
    @12
    @20
    simp131
    #
    cA
    cP
    cQ
    cT
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22g.u
    cdleme22g.g
    cdleme3fa
    syl132anc
    #
    cA
    @28
    c.or
    cK
    cF
    cG
    @28
    eqid
    #
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    @21
    @1
    @30
    @0
    @1
    @3
    @8
    @12
    @20
    simp11r
    @28
    cH
    cK
    cW
    @44
    cdleme22.h
    lhpbase
    syl
    @28
    cK
    c.le
    c.an
    @25
    cW
    @44
    cdleme22.l
    cdleme22.m
    latmle1
    syl3anc
    @21
    cV
    cS
    cT
    c.or
    co
    cW
    c.an
    co
    #
    @26
    @21
    @2
    @13
    @3
    @19
    @16
    cV
    @45
    wceq
    @34
    @37
    @41
    @9
    @12
    @13
    @16
    @19
    simp33
    @9
    @12
    @13
    @16
    @19
    simp32
    cA
    cS
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22d
    syl131anc
    @21
    @2
    @10
    @11
    @13
    @3
    @7
    @14
    wa
    @6
    @5
    @45
    @26
    wceq
    @34
    @35
    @36
    @37
    @41
    @21
    @7
    @14
    @38
    @14
    @15
    @13
    @19
    @9
    @12
    simp32l
    jca
    @39
    @42
    cA
    cP
    cQ
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22g.u
    cdleme22g.f
    cdleme22g.g
    cdleme16
    syl332anc
    eqtr2d
    @21
    @0
    @32
    @33
    @25
    @22
    wceq
    @31
    @40
    @43
    cA
    c.or
    cK
    cF
    cG
    cdleme22.j
    cdleme22.a
    hlatjcom
    syl3anc
    3brtr3d
    @21
    cK
    clc
    wcel
    #
    @17
    @32
    @33
    cV
    cG
    wne
    #
    @23
    @24
    wi
    @21
    @0
    @46
    @31
    cK
    hlcvl
    syl
    @17
    @18
    @13
    @16
    @9
    @12
    simp33l
    @40
    @43
    @21
    @18
    cG
    cW
    c.le
    wbr
    wn
    #
    @47
    @17
    @18
    @13
    @16
    @9
    @12
    simp33r
    @21
    @2
    @10
    @11
    @3
    @7
    @5
    @48
    @34
    @35
    @36
    @41
    @38
    @42
    cA
    cP
    cQ
    cT
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22g.u
    cdleme22g.g
    cdleme3
    syl132anc
    cV
    cG
    cW
    c.le
    nbrne2
    syl2anc
    cA
    cV
    cF
    cG
    c.or
    cK
    c.le
    cdleme22.l
    cdleme22.j
    cdleme22.a
    cvlatexch1
    syl131anc
    mpd
end
