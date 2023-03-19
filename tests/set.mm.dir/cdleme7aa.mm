include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp33.mm"
include "wi.mm"
include "simp11l.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp2lr.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "wceq.mm"
include "simp2l.mm"
include "simp32.mm"
include "cdleme4.mm"
include "hlatjcom.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "mtod.mm"

theorem cdleme7aa
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
  let cW: class W
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme4.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme4.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> -. R .<_ ( U .\/ S ) )

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
    #
    wn
    #
    w3a
    #
    w3a
    #
    cR
    cU
    cS
    c.or
    co
    c.le
    wbr
    #
    @18
    @7
    @14
    @15
    @17
    @19
    simp33
    @21
    @22
    cS
    cU
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    @18
    @21
    @0
    @8
    @11
    cU
    cA
    wcel
    #
    cR
    cU
    wne
    #
    @22
    @24
    wi
    @0
    @1
    @5
    @6
    @14
    @20
    simp11l
    #
    @8
    @9
    @13
    @7
    @20
    simp2ll
    #
    @11
    @12
    @10
    @7
    @20
    simp2rl
    @21
    @2
    @5
    @6
    @15
    @25
    @2
    @5
    @6
    @14
    @20
    simp11
    #
    @2
    @5
    @6
    @14
    @20
    simp12
    @2
    @5
    @6
    @14
    @20
    simp13
    #
    @7
    @14
    @15
    @17
    @19
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
    @21
    cU
    cW
    c.le
    wbr
    #
    @9
    @26
    @21
    cU
    @16
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme4.u
    @21
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
    @35
    wcel
    #
    @33
    cW
    c.le
    wbr
    @21
    @0
    @34
    @27
    cK
    hllat
    syl
    @21
    @0
    @3
    @6
    @36
    @27
    @3
    @4
    @2
    @6
    @14
    @20
    simp12l
    #
    @30
    cA
    @35
    c.or
    cK
    cP
    cQ
    @35
    eqid
    #
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @21
    @1
    @37
    @0
    @1
    @5
    @6
    @14
    @20
    simp11r
    @35
    cH
    cK
    cW
    @39
    cdleme4.h
    lhpbase
    syl
    @35
    cK
    c.le
    c.an
    @16
    cW
    @39
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    syl5eqbr
    @8
    @9
    @13
    @7
    @20
    simp2lr
    @32
    @9
    wa
    cU
    cR
    cU
    cR
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cR
    cS
    cU
    c.or
    cK
    c.le
    cdleme4.l
    cdleme4.j
    cdleme4.a
    hlatexch1
    syl131anc
    @21
    @16
    @23
    cS
    c.le
    @21
    @16
    cR
    cU
    c.or
    co
    #
    @23
    @21
    @2
    @3
    @6
    @10
    @17
    @16
    @40
    wceq
    @29
    @38
    @30
    @7
    @10
    @13
    @20
    simp2l
    @7
    @14
    @15
    @17
    @19
    simp32
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
    @21
    @0
    @8
    @25
    @40
    @23
    wceq
    @27
    @28
    @31
    cA
    c.or
    cK
    cR
    cU
    cdleme4.j
    cdleme4.a
    hlatjcom
    syl3anc
    eqtrd
    breq2d
    sylibrd
    mtod
end
