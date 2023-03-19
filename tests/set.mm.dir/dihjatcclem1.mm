include "cfv.mm"
include "co.mm"
include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "wceq.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "chlt.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "simpld.mm"
include "atbase.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "clat.mm"
include "hllat.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simprd.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "lsm4.mm"
include "syl122anc.mm"
include "intnand.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mtbid.mm"
include "hlatlej1.mm"
include "dihvalcq2.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "hlatlej2.mm"
include "oveq12d.mm"
include "lsmidm.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem dihjatcclem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume dihjatcclem.b: |- B = ( Base ` K )
  assume dihjatcclem.l: |- .<_ = ( le ` K )
  assume dihjatcclem.h: |- H = ( LHyp ` K )
  assume dihjatcclem.j: |- .\/ = ( join ` K )
  assume dihjatcclem.m: |- ./\ = ( meet ` K )
  assume dihjatcclem.a: |- A = ( Atoms ` K )
  assume dihjatcclem.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatcclem.s: |- .(+) = ( LSSum ` U )
  assume dihjatcclem.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjatcclem.v: |- V = ( ( P .\/ Q ) ./\ W )
  assume dihjatcclem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjatcclem.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dihjatcclem.q: |- ( ph -> ( Q e. A /\ -. Q .<_ W ) )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) = ( ( ( I ` P ) .(+) ( I ` Q ) ) .(+) ( I ` V ) ) )

  proof
    wph
    cP
    cI
    cfv
    #
    cV
    cI
    cfv
    #
    c.po
    co
    #
    cQ
    cI
    cfv
    #
    @1
    c.po
    co
    #
    c.po
    co
    #
    @0
    @3
    c.po
    co
    #
    @1
    @1
    c.po
    co
    #
    c.po
    co
    #
    cP
    cQ
    c.or
    co
    #
    cI
    cfv
    #
    @6
    @1
    c.po
    co
    wph
    cU
    cabl
    wcel
    #
    @0
    cU
    csubg
    cfv
    #
    wcel
    @1
    @12
    wcel
    #
    @3
    @12
    wcel
    @13
    @5
    @8
    wceq
    wph
    cU
    clmod
    wcel
    #
    @11
    wph
    cU
    cH
    cK
    cW
    dihjatcclem.h
    dihjatcclem.u
    dihjatcclem.k
    dvhlmod
    #
    cU
    lmodabl
    syl
    wph
    cU
    clss
    cfv
    #
    @12
    @0
    wph
    @14
    @16
    @12
    wss
    @15
    @16
    cU
    @16
    eqid
    #
    lsssssubg
    syl
    #
    wph
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
    cB
    wcel
    #
    @0
    @16
    wcel
    dihjatcclem.k
    wph
    cP
    cA
    wcel
    #
    @22
    wph
    @23
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    dihjatcclem.p
    simpld
    #
    cA
    cB
    cP
    cK
    dihjatcclem.b
    dihjatcclem.a
    atbase
    syl
    #
    cB
    @16
    cU
    cH
    cI
    cK
    cW
    cP
    dihjatcclem.b
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    @17
    dihlss
    syl2anc
    sseldd
    wph
    @16
    @12
    @1
    @18
    wph
    @21
    cV
    cB
    wcel
    @1
    @16
    wcel
    dihjatcclem.k
    wph
    cV
    @9
    cW
    c.an
    co
    #
    cB
    dihjatcclem.v
    wph
    cK
    clat
    wcel
    #
    @9
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @28
    cB
    wcel
    wph
    @19
    @29
    wph
    @19
    @20
    dihjatcclem.k
    simpld
    #
    cK
    hllat
    syl
    #
    wph
    @19
    @23
    cQ
    cA
    wcel
    #
    @30
    @32
    @26
    wph
    @34
    cQ
    cW
    c.le
    wbr
    #
    wn
    #
    dihjatcclem.q
    simpld
    #
    cA
    cB
    c.or
    cK
    cP
    cQ
    dihjatcclem.b
    dihjatcclem.j
    dihjatcclem.a
    hlatjcl
    syl3anc
    #
    wph
    @20
    @31
    wph
    @19
    @20
    dihjatcclem.k
    simprd
    cB
    cH
    cK
    cW
    dihjatcclem.b
    dihjatcclem.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    @9
    cW
    dihjatcclem.b
    dihjatcclem.m
    latmcl
    syl3anc
    syl5eqel
    cB
    @16
    cU
    cH
    cI
    cK
    cW
    cV
    dihjatcclem.b
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    @17
    dihlss
    syl2anc
    sseldd
    #
    wph
    @16
    @12
    @3
    @18
    wph
    @21
    cQ
    cB
    wcel
    #
    @3
    @16
    wcel
    dihjatcclem.k
    wph
    @34
    @41
    @37
    cA
    cB
    cQ
    cK
    dihjatcclem.b
    dihjatcclem.a
    atbase
    syl
    #
    cB
    @16
    cU
    cH
    cI
    cK
    cW
    cQ
    dihjatcclem.b
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    @17
    dihlss
    syl2anc
    sseldd
    @40
    c.po
    @0
    @1
    @3
    @1
    cU
    dihjatcclem.s
    lsm4
    syl122anc
    wph
    @10
    @10
    c.po
    co
    #
    @5
    @10
    wph
    @10
    @2
    @10
    @4
    c.po
    wph
    @10
    @0
    @28
    cI
    cfv
    #
    c.po
    co
    #
    @2
    wph
    @21
    @30
    @9
    cW
    c.le
    wbr
    #
    wn
    #
    @23
    @25
    wa
    cP
    @9
    c.le
    wbr
    #
    @10
    @45
    wceq
    dihjatcclem.k
    @38
    wph
    @24
    @35
    wa
    #
    @46
    wph
    @35
    @24
    wph
    @34
    @36
    dihjatcclem.q
    simprd
    intnand
    wph
    @29
    @22
    @41
    @31
    @49
    @46
    wb
    @33
    @27
    @42
    @39
    cB
    c.or
    cK
    c.le
    cP
    cQ
    cW
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.j
    latjle12
    syl13anc
    mtbid
    #
    dihjatcclem.p
    wph
    @19
    @23
    @34
    @48
    @32
    @26
    @37
    cA
    cP
    cQ
    c.or
    cK
    c.le
    dihjatcclem.l
    dihjatcclem.j
    dihjatcclem.a
    hlatlej1
    syl3anc
    cA
    cB
    c.po
    cP
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    @9
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.j
    dihjatcclem.m
    dihjatcclem.a
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    dihjatcclem.s
    dihvalcq2
    syl122anc
    @1
    @44
    @0
    c.po
    cV
    @28
    cI
    dihjatcclem.v
    fveq2i
    #
    oveq2i
    syl6eqr
    wph
    @10
    @3
    @44
    c.po
    co
    #
    @4
    wph
    @21
    @30
    @47
    @34
    @36
    wa
    cQ
    @9
    c.le
    wbr
    #
    @10
    @52
    wceq
    dihjatcclem.k
    @38
    @50
    dihjatcclem.q
    wph
    @19
    @23
    @34
    @53
    @32
    @26
    @37
    cA
    cP
    cQ
    c.or
    cK
    c.le
    dihjatcclem.l
    dihjatcclem.j
    dihjatcclem.a
    hlatlej2
    syl3anc
    cA
    cB
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    @9
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.j
    dihjatcclem.m
    dihjatcclem.a
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    dihjatcclem.s
    dihvalcq2
    syl122anc
    @1
    @44
    @3
    c.po
    @51
    oveq2i
    syl6eqr
    oveq12d
    wph
    @10
    @12
    wcel
    @43
    @10
    wceq
    wph
    @16
    @12
    @10
    @18
    wph
    @21
    @30
    @10
    @16
    wcel
    dihjatcclem.k
    @38
    cB
    @16
    cU
    cH
    cI
    cK
    cW
    @9
    dihjatcclem.b
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    @17
    dihlss
    syl2anc
    sseldd
    c.po
    @10
    cU
    dihjatcclem.s
    lsmidm
    syl
    eqtr3d
    wph
    @7
    @1
    @6
    c.po
    wph
    @13
    @7
    @1
    wceq
    @40
    c.po
    @1
    cU
    dihjatcclem.s
    lsmidm
    syl
    oveq2d
    3eqtr3d
end
