include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp2l.mm"
include "simp13.mm"
include "simp2r.mm"
include "cdlemi1.mm"
include "syl221anc.mm"
include "simp12.mm"
include "cdlemi2.mm"
include "syl231anc.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "simp11.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simp2rl.mm"
include "atbase.mm"
include "ltrncl.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "ltrncnv.mm"
include "ltrnco.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "ltrnat.mm"
include "ltrnel.mm"
include "3jca.mm"
include "eqid.mm"
include "cdlemh.mm"
include "simpld.mm"
include "syld3an2.mm"
include "atcmp.mm"
include "mpbid.mm"
include "syl6eqr.mm"

theorem cdlemi
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemi.b: |- B = ( Base ` K )
  assume cdlemi.l: |- .<_ = ( le ` K )
  assume cdlemi.j: |- .\/ = ( join ` K )
  assume cdlemi.m: |- ./\ = ( meet ` K )
  assume cdlemi.a: |- A = ( Atoms ` K )
  assume cdlemi.h: |- H = ( LHyp ` K )
  assume cdlemi.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemi.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemi.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemi.s: |- S = ( ( P .\/ ( R ` G ) ) ./\ ( ( ( U ` F ) ` P ) .\/ ( R ` ( G o. `' F ) ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( U e. E /\ ( P e. A /\ -. P .<_ W ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( ( U ` G ) ` P ) = S )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cU
    cE
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    cG
    @11
    wne
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    w3a
    #
    w3a
    #
    cP
    cG
    cU
    cfv
    #
    cfv
    #
    cP
    @13
    c.or
    co
    #
    cP
    cF
    cU
    cfv
    #
    cfv
    #
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cS
    @15
    @17
    @25
    c.le
    wbr
    #
    @17
    @25
    wceq
    #
    @15
    @17
    @18
    c.le
    wbr
    #
    @17
    @24
    c.le
    wbr
    #
    @26
    @15
    @0
    @1
    @6
    @4
    @9
    @28
    @0
    @1
    @3
    @4
    @10
    @14
    simp11l
    #
    @0
    @1
    @3
    @4
    @10
    @14
    simp11r
    #
    @5
    @6
    @9
    @14
    simp2l
    #
    @2
    @3
    @4
    @10
    @14
    simp13
    #
    @5
    @6
    @9
    @14
    simp2r
    #
    cA
    cB
    cP
    cR
    cT
    cU
    cE
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemi.b
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    cdlemi.h
    cdlemi.t
    cdlemi.r
    cdlemi.e
    cdlemi1
    syl221anc
    @15
    @0
    @1
    @6
    @3
    @4
    @9
    @29
    @30
    @31
    @32
    @2
    @3
    @4
    @10
    @14
    simp12
    #
    @33
    @34
    cA
    cB
    cP
    cR
    cT
    cU
    cE
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemi.b
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    cdlemi.h
    cdlemi.t
    cdlemi.r
    cdlemi.e
    cdlemi2
    syl231anc
    @15
    cK
    clat
    wcel
    #
    @17
    cB
    wcel
    #
    @18
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    @28
    @29
    wa
    @26
    wb
    @15
    @0
    @36
    @30
    cK
    hllat
    syl
    #
    @15
    @2
    @16
    cT
    wcel
    #
    cP
    cB
    wcel
    #
    @37
    @2
    @3
    @4
    @10
    @14
    simp11
    #
    @15
    @2
    @6
    @4
    @41
    @43
    @32
    @33
    cU
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    cdlemi.h
    cdlemi.t
    cdlemi.e
    tendocl
    syl3anc
    #
    @15
    @7
    @42
    @7
    @8
    @6
    @5
    @14
    simp2rl
    #
    cA
    cB
    cP
    cK
    cdlemi.b
    cdlemi.a
    atbase
    syl
    #
    cB
    cT
    @16
    cH
    cK
    chlt
    cW
    cP
    cdlemi.b
    cdlemi.h
    cdlemi.t
    ltrncl
    syl3anc
    @15
    @36
    @42
    @13
    cB
    wcel
    #
    @38
    @40
    @46
    @15
    @2
    @4
    @47
    @43
    @33
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemi.b
    cdlemi.h
    cdlemi.t
    cdlemi.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    cP
    @13
    cdlemi.b
    cdlemi.j
    latjcl
    syl3anc
    @15
    @36
    @20
    cB
    wcel
    #
    @23
    cB
    wcel
    #
    @39
    @40
    @15
    @2
    @19
    cT
    wcel
    #
    @42
    @48
    @43
    @15
    @2
    @6
    @3
    @50
    @43
    @32
    @35
    cU
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    cdlemi.h
    cdlemi.t
    cdlemi.e
    tendocl
    syl3anc
    #
    @46
    cB
    cT
    @19
    cH
    cK
    chlt
    cW
    cP
    cdlemi.b
    cdlemi.h
    cdlemi.t
    ltrncl
    syl3anc
    @15
    @2
    @22
    cT
    wcel
    #
    @49
    @43
    @15
    @2
    @4
    @21
    cT
    wcel
    #
    @52
    @43
    @33
    @15
    @2
    @3
    @53
    @43
    @35
    cT
    cF
    cH
    cK
    cW
    cdlemi.h
    cdlemi.t
    ltrncnv
    syl2anc
    cT
    cG
    @21
    cH
    cK
    cW
    cdlemi.h
    cdlemi.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @22
    cH
    cK
    cW
    cdlemi.b
    cdlemi.h
    cdlemi.t
    cdlemi.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    @20
    @23
    cdlemi.b
    cdlemi.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @17
    @18
    @24
    cdlemi.b
    cdlemi.l
    cdlemi.m
    latlem12
    syl13anc
    mpbi2and
    @15
    cK
    cal
    wcel
    #
    @17
    cA
    wcel
    #
    @25
    cA
    wcel
    #
    @26
    @27
    wb
    @15
    @0
    @54
    @30
    cK
    hlatl
    syl
    @15
    @2
    @41
    @7
    @55
    @43
    @44
    @45
    cA
    cP
    cT
    @16
    cH
    cK
    c.le
    cW
    cdlemi.l
    cdlemi.a
    cdlemi.h
    cdlemi.t
    ltrnat
    syl3anc
    @5
    @9
    @20
    cA
    wcel
    @20
    cW
    c.le
    wbr
    wn
    wa
    #
    @20
    cP
    @12
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    @10
    @14
    @56
    @15
    @9
    @57
    @58
    @34
    @15
    @2
    @50
    @9
    @57
    @43
    @51
    @34
    cA
    cP
    cT
    @19
    cH
    cK
    c.le
    cW
    cdlemi.l
    cdlemi.a
    cdlemi.h
    cdlemi.t
    ltrnel
    syl3anc
    @15
    @0
    @1
    @6
    @3
    @9
    @58
    @30
    @31
    @32
    @35
    @34
    cA
    cB
    cP
    cR
    cT
    cU
    cE
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemi.b
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    cdlemi.h
    cdlemi.t
    cdlemi.r
    cdlemi.e
    cdlemi1
    syl221anc
    3jca
    @5
    @59
    @14
    w3a
    @56
    @25
    cW
    c.le
    wbr
    wn
    cA
    cB
    cP
    @20
    cR
    @25
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemi.b
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    cdlemi.h
    cdlemi.t
    cdlemi.r
    @25
    eqid
    cdlemh
    simpld
    syld3an2
    cA
    @17
    @25
    cK
    c.le
    cdlemi.l
    cdlemi.a
    atcmp
    syl3anc
    mpbid
    cdlemi.s
    syl6eqr
end
