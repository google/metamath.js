include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp2r.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "atbase.mm"
include "latlej1.mm"
include "simp3l.mm"
include "wb.mm"
include "latjcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "latmcl.mm"
include "latmlem1.mm"
include "mpd.mm"
include "wceq.mm"
include "latlej2.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "oveq2d.mm"
include "latmlej22.mm"
include "atmod2i2.mm"
include "col.mm"
include "hlol.mm"
include "latmassOLD.mm"
include "3eqtr4rd.mm"
include "breqtrd.mm"

theorem dalawlem2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume dalawlem.l: |- .<_ = ( le ` K )
  assume dalawlem.j: |- .\/ = ( join ` K )
  assume dalawlem.m: |- ./\ = ( meet ` K )
  assume dalawlem.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A ) /\ ( S e. A /\ T e. A ) ) -> ( ( P .\/ Q ) ./\ ( S .\/ T ) ) .<_ ( ( ( ( P .\/ Q ) .\/ T ) ./\ S ) .\/ ( ( ( P .\/ Q ) .\/ S ) ./\ T ) ) )

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
    wa
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    c.an
    co
    #
    @8
    cT
    c.or
    co
    #
    @8
    cS
    c.or
    co
    #
    c.an
    co
    #
    @9
    c.an
    co
    #
    @11
    cS
    c.an
    co
    @12
    cT
    c.an
    co
    #
    c.or
    co
    #
    c.le
    @7
    @8
    @13
    c.le
    wbr
    #
    @10
    @14
    c.le
    wbr
    #
    @7
    @8
    @11
    c.le
    wbr
    #
    @8
    @12
    c.le
    wbr
    #
    @17
    @7
    cK
    clat
    wcel
    #
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    cT
    @22
    wcel
    #
    @19
    @7
    @0
    @21
    @0
    @3
    @6
    simp1
    #
    cK
    hllat
    syl
    #
    @7
    @0
    @1
    @2
    @23
    @25
    @0
    @1
    @2
    @6
    simp2l
    @0
    @1
    @2
    @6
    simp2r
    cA
    @22
    c.or
    cK
    cP
    cQ
    @22
    eqid
    #
    dalawlem.j
    dalawlem.a
    hlatjcl
    syl3anc
    #
    @7
    @5
    @24
    @0
    @3
    @4
    @5
    simp3r
    #
    cA
    @22
    cT
    cK
    @27
    dalawlem.a
    atbase
    syl
    #
    @22
    c.or
    cK
    c.le
    @8
    cT
    @27
    dalawlem.l
    dalawlem.j
    latlej1
    syl3anc
    @7
    @21
    @23
    cS
    @22
    wcel
    #
    @20
    @26
    @28
    @7
    @4
    @31
    @0
    @3
    @4
    @5
    simp3l
    #
    cA
    @22
    cS
    cK
    @27
    dalawlem.a
    atbase
    syl
    #
    @22
    c.or
    cK
    c.le
    @8
    cS
    @27
    dalawlem.l
    dalawlem.j
    latlej1
    syl3anc
    @7
    @21
    @23
    @11
    @22
    wcel
    #
    @12
    @22
    wcel
    #
    @19
    @20
    wa
    @17
    wb
    @26
    @28
    @7
    @21
    @23
    @24
    @34
    @26
    @28
    @30
    @22
    c.or
    cK
    @8
    cT
    @27
    dalawlem.j
    latjcl
    syl3anc
    #
    @7
    @21
    @23
    @31
    @35
    @26
    @28
    @33
    @22
    c.or
    cK
    @8
    cS
    @27
    dalawlem.j
    latjcl
    syl3anc
    #
    @22
    cK
    c.le
    c.an
    @8
    @11
    @12
    @27
    dalawlem.l
    dalawlem.m
    latlem12
    syl13anc
    mpbi2and
    @7
    @21
    @23
    @13
    @22
    wcel
    #
    @9
    @22
    wcel
    #
    @17
    @18
    wi
    @26
    @28
    @7
    @21
    @34
    @35
    @38
    @26
    @36
    @37
    @22
    cK
    c.an
    @11
    @12
    @27
    dalawlem.m
    latmcl
    syl3anc
    @7
    @0
    @4
    @5
    @39
    @25
    @32
    @29
    cA
    @22
    c.or
    cK
    cS
    cT
    @27
    dalawlem.j
    dalawlem.a
    hlatjcl
    syl3anc
    #
    @22
    cK
    c.le
    c.an
    @8
    @13
    @9
    @27
    dalawlem.l
    dalawlem.m
    latmlem1
    syl13anc
    mpd
    @7
    @11
    cS
    @15
    c.or
    co
    #
    c.an
    co
    #
    @11
    @12
    @9
    c.an
    co
    #
    c.an
    co
    #
    @16
    @14
    @7
    @41
    @43
    @11
    c.an
    @7
    @0
    @4
    @35
    @24
    cS
    @12
    c.le
    wbr
    #
    @41
    @43
    wceq
    @25
    @32
    @37
    @30
    @7
    @21
    @23
    @31
    @45
    @26
    @28
    @33
    @22
    c.or
    cK
    c.le
    @8
    cS
    @27
    dalawlem.l
    dalawlem.j
    latlej2
    syl3anc
    cA
    @22
    cS
    c.or
    cK
    c.le
    c.an
    @12
    cT
    @27
    dalawlem.l
    dalawlem.j
    dalawlem.m
    dalawlem.a
    atmod3i1
    syl131anc
    oveq2d
    @7
    @0
    @4
    @34
    @15
    @22
    wcel
    #
    @15
    @11
    c.le
    wbr
    #
    @16
    @42
    wceq
    @25
    @32
    @36
    @7
    @21
    @35
    @24
    @46
    @26
    @37
    @30
    @22
    cK
    c.an
    @12
    cT
    @27
    dalawlem.m
    latmcl
    syl3anc
    @7
    @21
    @24
    @35
    @23
    @47
    @26
    @30
    @37
    @28
    @22
    c.or
    cK
    c.le
    c.an
    cT
    @12
    @8
    @27
    dalawlem.l
    dalawlem.j
    dalawlem.m
    latmlej22
    syl13anc
    cA
    @22
    cS
    c.or
    cK
    c.le
    c.an
    @11
    @15
    @27
    dalawlem.l
    dalawlem.j
    dalawlem.m
    dalawlem.a
    atmod2i2
    syl131anc
    @7
    cK
    col
    wcel
    #
    @34
    @35
    @39
    @14
    @44
    wceq
    @7
    @0
    @48
    @25
    cK
    hlol
    syl
    @36
    @37
    @40
    @22
    cK
    c.an
    @11
    @12
    @9
    @27
    dalawlem.m
    latmassOLD
    syl13anc
    3eqtr4rd
    breqtrd
end
