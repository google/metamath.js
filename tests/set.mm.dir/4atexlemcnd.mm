include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "4atexlemtlw.mm"
include "4atexlemnclw.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wa.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "4atexlemk.mm"
include "4atexlemq.mm"
include "4atexlemt.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "w3a.mm"
include "simp221.mm"
include "sylbi.mm"
include "oveq12d.mm"
include "clc.mm"
include "4atexlemkc.mm"
include "4atexlemp.mm"
include "4atexlempnq.mm"
include "simp223.mm"
include "cvlsupr6.mm"
include "necomd.mm"
include "syl132anc.mm"
include "4atexlemntlpq.mm"
include "cvlsupr7.mm"
include "eqtr4d.mm"
include "breq2d.mm"
include "mtbid.mm"
include "2llnma2.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "4atexlemkl.mm"
include "4atexlemqtb.mm"
include "4atexlempsb.mm"
include "eqid.mm"
include "latmle1.mm"
include "syl5eqbr.mm"
include "simpr.mm"
include "hlatjcl.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "4atexlemc.mm"
include "atbase.mm"
include "syl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "eqeltrrd.mm"
include "atcmp.mm"
include "mpbid.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem 4atexlemcnd
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let vz: setvar z
  assume 4thatlem.ph: |- ( ph <-> ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( S e. A /\ ( R e. A /\ -. R .<_ W /\ ( P .\/ R ) = ( Q .\/ R ) ) /\ ( T e. A /\ ( U .\/ T ) = ( V .\/ T ) ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) )
  assume 4thatlem0.l: |- .<_ = ( le ` K )
  assume 4thatlem0.j: |- .\/ = ( join ` K )
  assume 4thatlem0.m: |- ./\ = ( meet ` K )
  assume 4thatlem0.a: |- A = ( Atoms ` K )
  assume 4thatlem0.h: |- H = ( LHyp ` K )
  assume 4thatlem0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume 4thatlem0.v: |- V = ( ( P .\/ S ) ./\ W )
  assume 4thatlem0.c: |- C = ( ( Q .\/ T ) ./\ ( P .\/ S ) )
  assume 4thatlem0.d: |- D = ( ( R .\/ T ) ./\ ( P .\/ S ) )


  assert |- ( ph -> C =/= D )

  proof
    wph
    cT
    cC
    wne
    #
    cC
    cD
    wne
    wph
    cT
    cW
    c.le
    wbr
    cC
    cW
    c.le
    wbr
    wn
    @0
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4thatlem0.v
    4atexlemtlw
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4thatlem0.v
    4thatlem0.c
    4atexlemnclw
    cT
    cC
    cW
    c.le
    nbrne2
    syl2anc
    wph
    cC
    cD
    cT
    cC
    wph
    cC
    cD
    wceq
    #
    cT
    cC
    wceq
    wph
    @1
    wa
    #
    cT
    cQ
    cT
    c.or
    co
    #
    cR
    cT
    c.or
    co
    #
    c.an
    co
    #
    cC
    wph
    cT
    @5
    wceq
    @1
    wph
    @5
    cT
    cQ
    c.or
    co
    #
    cT
    cR
    c.or
    co
    #
    c.an
    co
    #
    cT
    wph
    @3
    @6
    @4
    @7
    c.an
    wph
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    @3
    @6
    wceq
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemk
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemq
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemt
    #
    cA
    c.or
    cK
    cQ
    cT
    4thatlem0.j
    4thatlem0.a
    hlatjcom
    syl3anc
    wph
    @9
    cR
    cA
    wcel
    #
    @11
    @4
    @7
    wceq
    @12
    wph
    @9
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    wa
    @10
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cS
    cA
    wcel
    #
    @15
    cR
    cW
    c.le
    wbr
    wn
    #
    cP
    cR
    c.or
    co
    cQ
    cR
    c.or
    co
    #
    wceq
    #
    w3a
    @11
    cU
    cT
    c.or
    co
    cV
    cT
    c.or
    co
    wceq
    wa
    #
    w3a
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    @15
    4thatlem.ph
    @15
    @19
    @21
    @18
    @22
    @17
    @25
    simp221
    sylbi
    #
    @14
    cA
    c.or
    cK
    cR
    cT
    4thatlem0.j
    4thatlem0.a
    hlatjcom
    syl3anc
    oveq12d
    wph
    @9
    @10
    @15
    @11
    cQ
    cR
    wne
    #
    cT
    @20
    c.le
    wbr
    #
    wn
    @8
    cT
    wceq
    @12
    @13
    @27
    @14
    wph
    cK
    clc
    wcel
    #
    @16
    @10
    @15
    @23
    @21
    @28
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemkc
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemp
    #
    @13
    @27
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlempnq
    #
    wph
    @26
    @21
    4thatlem.ph
    @15
    @19
    @21
    @18
    @22
    @17
    @25
    simp223
    sylbi
    #
    @30
    @16
    @10
    @15
    w3a
    @23
    @21
    wa
    w3a
    cR
    cQ
    cA
    cP
    cQ
    cR
    c.or
    cK
    4thatlem0.a
    4thatlem0.j
    cvlsupr6
    necomd
    syl132anc
    wph
    cT
    @24
    c.le
    wbr
    @29
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4thatlem0.v
    4atexlemntlpq
    wph
    @24
    @20
    cT
    c.le
    wph
    @24
    cR
    cQ
    c.or
    co
    #
    @20
    wph
    @30
    @16
    @10
    @15
    @23
    @21
    @24
    @35
    wceq
    @31
    @32
    @13
    @27
    @33
    @34
    cA
    cP
    cQ
    cR
    c.or
    cK
    4thatlem0.a
    4thatlem0.j
    cvlsupr7
    syl132anc
    wph
    @9
    @10
    @15
    @20
    @35
    wceq
    @12
    @13
    @27
    cA
    c.or
    cK
    cQ
    cR
    4thatlem0.j
    4thatlem0.a
    hlatjcom
    syl3anc
    eqtr4d
    breq2d
    mtbid
    cA
    cQ
    cR
    cT
    c.or
    cK
    c.le
    c.an
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    2llnma2
    syl132anc
    eqtr2d
    #
    adantr
    @2
    cC
    @5
    c.le
    wbr
    #
    cC
    @5
    wceq
    #
    @2
    cC
    @3
    c.le
    wbr
    #
    cC
    @4
    c.le
    wbr
    #
    @37
    wph
    @39
    @1
    wph
    cC
    @3
    cP
    cS
    c.or
    co
    #
    c.an
    co
    #
    @3
    c.le
    4thatlem0.c
    wph
    cK
    clat
    wcel
    #
    @3
    cK
    cbs
    cfv
    #
    wcel
    #
    @41
    @44
    wcel
    #
    @42
    @3
    c.le
    wbr
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemkl
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4thatlem0.j
    4thatlem0.a
    4atexlemqtb
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4thatlem0.j
    4thatlem0.a
    4atexlempsb
    #
    @44
    cK
    c.le
    c.an
    @3
    @41
    @44
    eqid
    #
    4thatlem0.l
    4thatlem0.m
    latmle1
    syl3anc
    syl5eqbr
    adantr
    @2
    cC
    cD
    @4
    c.le
    wph
    @1
    simpr
    wph
    cD
    @4
    c.le
    wbr
    @1
    wph
    cD
    @4
    @41
    c.an
    co
    #
    @4
    c.le
    4thatlem0.d
    wph
    @43
    @4
    @44
    wcel
    #
    @46
    @51
    @4
    c.le
    wbr
    @47
    wph
    @9
    @15
    @11
    @52
    @12
    @27
    @14
    cA
    @44
    c.or
    cK
    cR
    cT
    @50
    4thatlem0.j
    4thatlem0.a
    hlatjcl
    syl3anc
    #
    @49
    @44
    cK
    c.le
    c.an
    @4
    @41
    @50
    4thatlem0.l
    4thatlem0.m
    latmle1
    syl3anc
    syl5eqbr
    adantr
    eqbrtrd
    wph
    @39
    @40
    wa
    @37
    wb
    #
    @1
    wph
    @43
    cC
    @44
    wcel
    #
    @45
    @52
    @54
    @47
    wph
    cC
    cA
    wcel
    #
    @55
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4thatlem0.v
    4thatlem0.c
    4atexlemc
    #
    cA
    @44
    cC
    cK
    @50
    4thatlem0.a
    atbase
    syl
    @48
    @53
    @44
    cK
    c.le
    c.an
    cC
    @3
    @4
    @50
    4thatlem0.l
    4thatlem0.m
    latlem12
    syl13anc
    adantr
    mpbi2and
    wph
    @37
    @38
    wb
    #
    @1
    wph
    cK
    cal
    wcel
    #
    @56
    @5
    cA
    wcel
    @58
    wph
    @9
    @59
    @12
    cK
    hlatl
    syl
    @57
    wph
    cT
    @5
    cA
    @36
    @14
    eqeltrrd
    cA
    cC
    @5
    cK
    c.le
    4thatlem0.l
    4thatlem0.a
    atcmp
    syl3anc
    adantr
    mpbid
    eqtr4d
    ex
    necon3d
    mpd
end
