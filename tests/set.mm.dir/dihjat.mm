include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "simprl.mm"
include "jca.mm"
include "simprr.mm"
include "dihjatb.mm"
include "wn.mm"
include "cbs.mm"
include "atbase.mm"
include "syl.mm"
include "dihjatc.mm"
include "simpld.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "cabl.mm"
include "csubg.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodabl.mm"
include "clss.mm"
include "wss.mm"
include "lsssssubg.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "lsmcom.mm"
include "3eqtr4d.mm"
include "dihjatcc.mm"
include "4casesdan.mm"

theorem dihjat
  let wph: wff ph
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cW: class W
  assume dihjat.h: |- H = ( LHyp ` K )
  assume dihjat.j: |- .\/ = ( join ` K )
  assume dihjat.a: |- A = ( Atoms ` K )
  assume dihjat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat.s: |- .(+) = ( LSSum ` U )
  assume dihjat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat.p: |- ( ph -> P e. A )
  assume dihjat.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) = ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    cP
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    cQ
    cW
    @0
    wbr
    #
    cP
    cQ
    c.or
    co
    #
    cI
    cfv
    #
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
    wceq
    wph
    @1
    @2
    wa
    #
    wa
    #
    cA
    cP
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    @0
    cW
    @0
    eqid
    #
    dihjat.h
    dihjat.j
    dihjat.a
    dihjat.u
    dihjat.s
    dihjat.i
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
    @8
    dihjat.k
    adantr
    @9
    cP
    cA
    wcel
    #
    @1
    wph
    @14
    @8
    dihjat.p
    adantr
    wph
    @1
    @2
    simprl
    jca
    @9
    cQ
    cA
    wcel
    #
    @2
    wph
    @15
    @8
    dihjat.q
    adantr
    wph
    @1
    @2
    simprr
    jca
    dihjatb
    wph
    @1
    @2
    wn
    #
    wa
    #
    wa
    #
    cA
    cK
    cbs
    cfv
    #
    cQ
    c.po
    cU
    cH
    cI
    c.or
    cK
    @0
    cW
    cP
    @19
    eqid
    #
    @10
    dihjat.h
    dihjat.j
    dihjat.a
    dihjat.u
    dihjat.s
    dihjat.i
    wph
    @13
    @17
    dihjat.k
    adantr
    @18
    cP
    @19
    wcel
    #
    @1
    wph
    @21
    @17
    wph
    @14
    @21
    dihjat.p
    cA
    @19
    cP
    cK
    @20
    dihjat.a
    atbase
    syl
    #
    adantr
    wph
    @1
    @16
    simprl
    jca
    @18
    @15
    @16
    wph
    @15
    @17
    dihjat.q
    adantr
    wph
    @1
    @16
    simprr
    jca
    dihjatc
    wph
    @1
    wn
    #
    @2
    wa
    #
    wa
    #
    cQ
    cP
    c.or
    co
    #
    cI
    cfv
    #
    @6
    @5
    c.po
    co
    #
    @4
    @7
    @25
    cA
    @19
    cP
    c.po
    cU
    cH
    cI
    c.or
    cK
    @0
    cW
    cQ
    @20
    @10
    dihjat.h
    dihjat.j
    dihjat.a
    dihjat.u
    dihjat.s
    dihjat.i
    wph
    @13
    @24
    dihjat.k
    adantr
    @25
    cQ
    @19
    wcel
    #
    @2
    wph
    @29
    @24
    wph
    @15
    @29
    dihjat.q
    cA
    @19
    cQ
    cK
    @20
    dihjat.a
    atbase
    syl
    #
    adantr
    wph
    @23
    @2
    simprr
    jca
    @25
    @14
    @23
    wph
    @14
    @24
    dihjat.p
    adantr
    wph
    @23
    @2
    simprl
    jca
    dihjatc
    wph
    @4
    @27
    wceq
    @24
    wph
    @3
    @26
    cI
    wph
    @11
    @14
    @15
    @3
    @26
    wceq
    wph
    @11
    @12
    dihjat.k
    simpld
    dihjat.p
    dihjat.q
    cA
    c.or
    cK
    cP
    cQ
    dihjat.j
    dihjat.a
    hlatjcom
    syl3anc
    fveq2d
    adantr
    wph
    @7
    @28
    wceq
    #
    @24
    wph
    cU
    cabl
    wcel
    #
    @5
    cU
    csubg
    cfv
    #
    wcel
    @6
    @33
    wcel
    @31
    wph
    cU
    clmod
    wcel
    #
    @32
    wph
    cU
    cH
    cK
    cW
    dihjat.h
    dihjat.u
    dihjat.k
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
    @33
    @5
    wph
    @34
    @36
    @33
    wss
    @35
    @36
    cU
    @36
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @13
    @21
    @5
    @36
    wcel
    dihjat.k
    @22
    @19
    @36
    cU
    cH
    cI
    cK
    cW
    cP
    @20
    dihjat.h
    dihjat.i
    dihjat.u
    @37
    dihlss
    syl2anc
    sseldd
    wph
    @36
    @33
    @6
    @38
    wph
    @13
    @29
    @6
    @36
    wcel
    dihjat.k
    @30
    @19
    @36
    cU
    cH
    cI
    cK
    cW
    cQ
    @20
    dihjat.h
    dihjat.i
    dihjat.u
    @37
    dihlss
    syl2anc
    sseldd
    c.po
    @5
    @6
    cU
    dihjat.s
    lsmcom
    syl3anc
    adantr
    3eqtr4d
    wph
    @23
    @16
    wa
    #
    wa
    #
    cA
    cP
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    @0
    cW
    @10
    dihjat.h
    dihjat.j
    dihjat.a
    dihjat.u
    dihjat.s
    dihjat.i
    wph
    @13
    @39
    dihjat.k
    adantr
    @40
    @14
    @23
    wph
    @14
    @39
    dihjat.p
    adantr
    wph
    @23
    @16
    simprl
    jca
    @40
    @15
    @16
    wph
    @15
    @39
    dihjat.q
    adantr
    wph
    @23
    @16
    simprr
    jca
    dihjatcc
    4casesdan
end
