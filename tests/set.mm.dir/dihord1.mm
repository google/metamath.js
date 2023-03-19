include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2r.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "jca.mm"
include "simp12l.mm"
include "atbase.mm"
include "simp2l.mm"
include "latjcl.mm"
include "latlej1.mm"
include "simp31.mm"
include "simp33.mm"
include "eqbrtrd.mm"
include "lattrd.mm"
include "simp32.mm"
include "breqtrrd.mm"
include "cdlemn5.mm"
include "syl131anc.mm"
include "wi.mm"
include "latmlem1.mm"
include "syl13anc.mm"
include "mpd.mm"
include "wb.mm"
include "dibord.mm"
include "syl122anc.mm"
include "mpbird.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "diclss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmub2.mm"
include "sstrd.mm"
include "lsmcl.mm"
include "lsmlub.mm"
include "mpbi2and.mm"

theorem dihord1
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihjust.b: |- B = ( Base ` K )
  assume dihjust.l: |- .<_ = ( le ` K )
  assume dihjust.j: |- .\/ = ( join ` K )
  assume dihjust.m: |- ./\ = ( meet ` K )
  assume dihjust.a: |- A = ( Atoms ` K )
  assume dihjust.h: |- H = ( LHyp ` K )
  assume dihjust.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dihjust.J: |- J = ( ( DIsoC ` K ) ` W )
  assume dihjust.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjust.s: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( Q .\/ ( X ./\ W ) ) = X /\ ( R .\/ ( Y ./\ W ) ) = Y /\ X .<_ Y ) ) -> ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` R ) .(+) ( I ` ( Y ./\ W ) ) ) )

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
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    cR
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cY
    wceq
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cQ
    cJ
    cfv
    #
    cR
    cJ
    cfv
    #
    @14
    cI
    cfv
    #
    c.po
    co
    #
    wss
    #
    @11
    cI
    cfv
    #
    @23
    wss
    #
    @20
    @25
    c.po
    co
    @23
    wss
    #
    @19
    @2
    @6
    @5
    @14
    cB
    wcel
    #
    @14
    cW
    c.le
    wbr
    #
    wa
    cQ
    @15
    c.le
    wbr
    @24
    @2
    @5
    @6
    @10
    @18
    simp11
    #
    @2
    @5
    @6
    @10
    @18
    simp13
    #
    @2
    @5
    @6
    @10
    @18
    simp12
    #
    @19
    @28
    @29
    @19
    cK
    clat
    wcel
    #
    @9
    cW
    cB
    wcel
    #
    @28
    @19
    @0
    @33
    @0
    @1
    @5
    @6
    @10
    @18
    simp11l
    cK
    hllat
    syl
    #
    @7
    @8
    @9
    @18
    simp2r
    #
    @19
    @1
    @34
    @0
    @1
    @5
    @6
    @10
    @18
    simp11r
    cB
    cH
    cK
    cW
    dihjust.b
    dihjust.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cY
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    #
    @19
    @33
    @9
    @34
    @29
    @35
    @36
    @37
    cB
    cK
    c.le
    c.an
    cY
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
    #
    jca
    @19
    cQ
    cY
    @15
    c.le
    @19
    cB
    cK
    c.le
    cQ
    @12
    cY
    dihjust.b
    dihjust.l
    @35
    @19
    @3
    cQ
    cB
    wcel
    #
    @3
    @4
    @2
    @6
    @10
    @18
    simp12l
    cA
    cB
    cQ
    cK
    dihjust.b
    dihjust.a
    atbase
    syl
    #
    @19
    @33
    @40
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    @35
    @41
    @19
    @33
    @8
    @34
    @42
    @35
    @7
    @8
    @9
    @18
    simp2l
    #
    @37
    cB
    cK
    c.an
    cX
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    #
    cB
    c.or
    cK
    cQ
    @11
    dihjust.b
    dihjust.j
    latjcl
    syl3anc
    @36
    @19
    @33
    @40
    @42
    cQ
    @12
    c.le
    wbr
    @35
    @41
    @44
    cB
    c.or
    cK
    c.le
    cQ
    @11
    dihjust.b
    dihjust.l
    dihjust.j
    latlej1
    syl3anc
    @19
    @12
    cX
    cY
    c.le
    @7
    @10
    @13
    @16
    @17
    simp31
    @7
    @10
    @13
    @16
    @17
    simp33
    #
    eqbrtrd
    lattrd
    @7
    @10
    @13
    @16
    @17
    simp32
    breqtrrd
    cA
    cB
    c.po
    cR
    cQ
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cW
    @14
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.a
    dihjust.h
    dihjust.u
    dihjust.s
    dihjust.i
    dihjust.J
    cdlemn5
    syl131anc
    @19
    @25
    @22
    @23
    @19
    @25
    @22
    wss
    #
    @11
    @14
    c.le
    wbr
    #
    @19
    @17
    @47
    @45
    @19
    @33
    @8
    @9
    @34
    @17
    @47
    wi
    @35
    @43
    @36
    @37
    cB
    cK
    c.le
    c.an
    cX
    cY
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmlem1
    syl13anc
    mpd
    @19
    @2
    @42
    @11
    cW
    c.le
    wbr
    #
    @28
    @29
    @46
    @47
    wb
    @30
    @44
    @19
    @33
    @8
    @34
    @48
    @35
    @43
    @37
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
    #
    @38
    @39
    cB
    cH
    cI
    cK
    c.le
    cW
    @11
    @14
    dihjust.b
    dihjust.l
    dihjust.h
    dihjust.i
    dibord
    syl122anc
    mpbird
    @19
    @21
    cU
    csubg
    cfv
    #
    wcel
    @22
    @50
    wcel
    @22
    @23
    wss
    @19
    cU
    clss
    cfv
    #
    @50
    @21
    @19
    cU
    clmod
    wcel
    #
    @51
    @50
    wss
    @19
    cU
    cH
    cK
    cW
    dihjust.h
    dihjust.u
    @30
    dvhlmod
    #
    @51
    cU
    @51
    eqid
    #
    lsssssubg
    syl
    #
    @19
    @2
    @6
    @21
    @51
    wcel
    #
    @30
    @31
    cA
    cR
    @51
    cU
    cH
    cJ
    cK
    c.le
    cW
    dihjust.l
    dihjust.a
    dihjust.h
    dihjust.u
    dihjust.J
    @54
    diclss
    syl2anc
    #
    sseldd
    @19
    @51
    @50
    @22
    @55
    @19
    @2
    @28
    @29
    @22
    @51
    wcel
    #
    @30
    @38
    @39
    cB
    @51
    cU
    cH
    cI
    cK
    c.le
    cW
    @14
    dihjust.b
    dihjust.l
    dihjust.h
    dihjust.u
    dihjust.i
    @54
    diblss
    syl12anc
    #
    sseldd
    c.po
    @21
    @22
    cU
    dihjust.s
    lsmub2
    syl2anc
    sstrd
    @19
    @20
    @50
    wcel
    @25
    @50
    wcel
    @23
    @50
    wcel
    @24
    @26
    wa
    @27
    wb
    @19
    @51
    @50
    @20
    @55
    @19
    @2
    @5
    @20
    @51
    wcel
    @30
    @32
    cA
    cQ
    @51
    cU
    cH
    cJ
    cK
    c.le
    cW
    dihjust.l
    dihjust.a
    dihjust.h
    dihjust.u
    dihjust.J
    @54
    diclss
    syl2anc
    sseldd
    @19
    @51
    @50
    @25
    @55
    @19
    @2
    @42
    @48
    @25
    @51
    wcel
    @30
    @44
    @49
    cB
    @51
    cU
    cH
    cI
    cK
    c.le
    cW
    @11
    dihjust.b
    dihjust.l
    dihjust.h
    dihjust.u
    dihjust.i
    @54
    diblss
    syl12anc
    sseldd
    @19
    @51
    @50
    @23
    @55
    @19
    @52
    @56
    @58
    @23
    @51
    wcel
    @53
    @57
    @59
    c.po
    @51
    @21
    @22
    cU
    @54
    dihjust.s
    lsmcl
    syl3anc
    sseldd
    c.po
    @20
    @25
    @23
    cU
    dihjust.s
    lsmlub
    syl3anc
    mpbi2and
end
