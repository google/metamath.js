include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "oveq12i.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp32.mm"
include "cdleme4.mm"
include "syl131anc.mm"
include "oveq1d.mm"
include "simp11l.mm"
include "simp12.mm"
include "simp31.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "simp2rl.mm"
include "simp2ll.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp2rr.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "cdleme7aa.mm"
include "2llnma2.mm"
include "syl132anc.mm"
include "eqtrd.mm"
include "col.mm"
include "hlol.mm"
include "latmmdir.mm"
include "syl13anc.mm"
include "lhpmat.mm"
include "3eqtr3d.mm"
include "syl5eq.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "simp33.mm"
include "cdleme7b.mm"
include "syl113anc.mm"
include "atnem0.mm"
include "mpbird.mm"

theorem cdleme7c
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
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
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme4.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme4.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme7.v: |- V = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> U =/= V )

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
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
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
    cS
    @16
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cU
    cV
    wne
    #
    cU
    cV
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    wceq
    #
    @20
    @22
    @16
    cW
    c.an
    co
    #
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.an
    co
    #
    @23
    cU
    @25
    cV
    @27
    c.an
    cdleme4.u
    cdleme7.v
    oveq12i
    @20
    @16
    @26
    c.an
    co
    #
    cW
    c.an
    co
    #
    cR
    cW
    c.an
    co
    #
    @28
    @23
    @20
    @29
    cR
    cW
    c.an
    @20
    @29
    cR
    cU
    c.or
    co
    #
    @26
    c.an
    co
    #
    cR
    @20
    @16
    @32
    @26
    c.an
    @20
    @2
    @3
    @6
    @10
    @17
    @16
    @32
    wceq
    @2
    @5
    @6
    @14
    @19
    simp11
    #
    @3
    @4
    @2
    @6
    @14
    @19
    simp12l
    #
    @2
    @5
    @6
    @14
    @19
    simp13
    #
    @7
    @10
    @13
    @19
    simp2l
    #
    @7
    @14
    @15
    @17
    @18
    simp32
    #
    cA
    cP
    cQ
    cR
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4
    syl131anc
    oveq1d
    @20
    @0
    cU
    cA
    wcel
    #
    @11
    @8
    cU
    cS
    wne
    #
    cR
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    @33
    cR
    wceq
    @0
    @1
    @5
    @6
    @14
    @19
    simp11l
    #
    @20
    @2
    @5
    @6
    @15
    @39
    @34
    @2
    @5
    @6
    @14
    @19
    simp12
    @36
    @7
    @14
    @15
    @17
    @18
    simp31
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    lhpat2
    syl112anc
    #
    @11
    @12
    @10
    @7
    @19
    simp2rl
    #
    @8
    @9
    @13
    @7
    @19
    simp2ll
    #
    @20
    cU
    cW
    c.le
    wbr
    @12
    @40
    @20
    cU
    @25
    cW
    c.le
    cdleme4.u
    @20
    cK
    clat
    wcel
    #
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @46
    wcel
    #
    @25
    cW
    c.le
    wbr
    @20
    @0
    @45
    @41
    cK
    hllat
    syl
    @20
    @0
    @3
    @6
    @47
    @41
    @35
    @36
    cA
    @46
    c.or
    cK
    cP
    cQ
    @46
    eqid
    #
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    #
    @20
    @1
    @48
    @0
    @1
    @5
    @6
    @14
    @19
    simp11r
    @46
    cH
    cK
    cW
    @49
    cdleme4.h
    lhpbase
    syl
    #
    @46
    cK
    c.le
    c.an
    @16
    cW
    @49
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    syl5eqbr
    @11
    @12
    @10
    @7
    @19
    simp2rr
    cU
    cS
    cW
    c.le
    nbrne2
    syl2anc
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme7aa
    cA
    cU
    cS
    cR
    c.or
    cK
    c.le
    c.an
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    2llnma2
    syl132anc
    eqtrd
    oveq1d
    @20
    cK
    col
    wcel
    #
    @47
    @26
    @46
    wcel
    #
    @48
    @30
    @28
    wceq
    @20
    @0
    @52
    @41
    cK
    hlol
    syl
    @50
    @20
    @0
    @8
    @11
    @53
    @41
    @44
    @43
    cA
    @46
    c.or
    cK
    cR
    cS
    @49
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @51
    @46
    cK
    c.an
    @16
    @26
    cW
    @49
    cdleme4.m
    latmmdir
    syl13anc
    @20
    @2
    @10
    @31
    @23
    wceq
    @34
    @37
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @23
    cdleme4.l
    cdleme4.m
    @23
    eqid
    #
    cdleme4.a
    cdleme4.h
    lhpmat
    syl2anc
    3eqtr3d
    syl5eq
    @20
    cK
    cal
    wcel
    #
    @39
    cV
    cA
    wcel
    #
    @21
    @24
    wb
    @20
    @0
    @55
    @41
    cK
    hlatl
    syl
    @42
    @20
    @2
    @10
    @11
    @18
    @17
    @56
    @34
    @37
    @43
    @7
    @14
    @15
    @17
    @18
    simp33
    @38
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme7.v
    cdleme7b
    syl113anc
    cA
    cU
    cV
    cK
    c.an
    @23
    cdleme4.m
    @54
    cdleme4.a
    atnem0
    syl3anc
    mpbird
end
