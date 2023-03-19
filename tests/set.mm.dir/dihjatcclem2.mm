include "co.mm"
include "cfv.mm"
include "dihjatcclem1.mm"
include "csubg.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "chlt.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "simpld.mm"
include "atbase.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "fveq2i.mm"
include "clat.mm"
include "hllat.mm"
include "hlatjcl.mm"
include "simprd.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "lsmss2.mm"
include "eqtrd.mm"

theorem dihjatcclem2
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
  assume dihjatcclem2.c: |- ( ph -> ( I ` V ) C_ ( ( I ` P ) .(+) ( I ` Q ) ) )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) = ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    cP
    cQ
    c.or
    co
    #
    cI
    cfv
    cP
    cI
    cfv
    #
    cQ
    cI
    cfv
    #
    c.po
    co
    #
    cV
    cI
    cfv
    #
    c.po
    co
    #
    @3
    wph
    cA
    cB
    cP
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cV
    cW
    dihjatcclem.b
    dihjatcclem.l
    dihjatcclem.h
    dihjatcclem.j
    dihjatcclem.m
    dihjatcclem.a
    dihjatcclem.u
    dihjatcclem.s
    dihjatcclem.i
    dihjatcclem.v
    dihjatcclem.k
    dihjatcclem.p
    dihjatcclem.q
    dihjatcclem1
    wph
    @3
    cU
    csubg
    cfv
    #
    wcel
    @4
    @6
    wcel
    @4
    @3
    wss
    @5
    @3
    wceq
    wph
    cU
    clss
    cfv
    #
    @6
    @3
    wph
    cU
    clmod
    wcel
    #
    @7
    @6
    wss
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
    @7
    cU
    @7
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @8
    @1
    @7
    wcel
    #
    @2
    @7
    wcel
    #
    @3
    @7
    wcel
    @9
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
    @12
    dihjatcclem.k
    wph
    cP
    cA
    wcel
    #
    @17
    wph
    @18
    cP
    cW
    c.le
    wbr
    wn
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
    cB
    @7
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
    @10
    dihlss
    syl2anc
    wph
    @16
    cQ
    cB
    wcel
    #
    @13
    dihjatcclem.k
    wph
    cQ
    cA
    wcel
    #
    @20
    wph
    @21
    cQ
    cW
    c.le
    wbr
    wn
    dihjatcclem.q
    simpld
    #
    cA
    cB
    cQ
    cK
    dihjatcclem.b
    dihjatcclem.a
    atbase
    syl
    cB
    @7
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
    @10
    dihlss
    syl2anc
    c.po
    @7
    @1
    @2
    cU
    @10
    dihjatcclem.s
    lsmcl
    syl3anc
    sseldd
    wph
    @7
    @6
    @4
    @11
    wph
    @4
    @0
    cW
    c.an
    co
    #
    cI
    cfv
    #
    @7
    cV
    @23
    cI
    dihjatcclem.v
    fveq2i
    wph
    @16
    @23
    cB
    wcel
    #
    @24
    @7
    wcel
    dihjatcclem.k
    wph
    cK
    clat
    wcel
    #
    @0
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @25
    wph
    @14
    @26
    wph
    @14
    @15
    dihjatcclem.k
    simpld
    #
    cK
    hllat
    syl
    wph
    @14
    @18
    @21
    @27
    @29
    @19
    @22
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
    wph
    @15
    @28
    wph
    @14
    @15
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
    cB
    cK
    c.an
    @0
    cW
    dihjatcclem.b
    dihjatcclem.m
    latmcl
    syl3anc
    cB
    @7
    cU
    cH
    cI
    cK
    cW
    @23
    dihjatcclem.b
    dihjatcclem.h
    dihjatcclem.i
    dihjatcclem.u
    @10
    dihlss
    syl2anc
    syl5eqel
    sseldd
    dihjatcclem2.c
    c.po
    @3
    @4
    cU
    dihjatcclem.s
    lsmss2
    syl3anc
    eqtrd
end
