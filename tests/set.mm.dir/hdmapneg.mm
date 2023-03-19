include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "c0g.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "hdmapcl.mm"
include "lmodvnegid.mm"
include "syl2anc.mm"
include "dvhlmod.mm"
include "lmodvnegcl.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "hdmapeq0.mm"
include "mpbird.mm"
include "hdmapadd.mm"
include "3eqtr2rd.mm"
include "wb.mm"
include "lmodlcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem hdmapneg
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  assume hdmap12b.h: |- H = ( LHyp ` K )
  assume hdmap12b.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap12b.v: |- V = ( Base ` U )
  assume hdmap12b.m: |- M = ( invg ` U )
  assume hdmap12b.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap12b.i: |- I = ( invg ` C )
  assume hdmap12b.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap12b.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap12b.x: |- ( ph -> T e. V )


  assert |- ( ph -> ( S ` ( M ` T ) ) = ( I ` ( S ` T ) ) )

  proof
    wph
    cT
    cS
    cfv
    #
    cT
    cM
    cfv
    #
    cS
    cfv
    #
    cC
    cplusg
    cfv
    #
    co
    #
    @0
    @0
    cI
    cfv
    #
    @3
    co
    #
    wceq
    #
    @2
    @5
    wceq
    #
    wph
    @6
    cC
    c0g
    cfv
    #
    cT
    @1
    cU
    cplusg
    cfv
    #
    co
    #
    cS
    cfv
    #
    @4
    wph
    cC
    clmod
    wcel
    #
    @0
    cC
    cbs
    cfv
    #
    wcel
    #
    @6
    @9
    wceq
    wph
    cC
    cH
    cK
    cW
    hdmap12b.h
    hdmap12b.c
    hdmap12b.k
    lcdlmod
    #
    wph
    cC
    @14
    cS
    cT
    cU
    cH
    cK
    cV
    cW
    hdmap12b.h
    hdmap12b.u
    hdmap12b.v
    hdmap12b.c
    @14
    eqid
    #
    hdmap12b.s
    hdmap12b.k
    hdmap12b.x
    hdmapcl
    #
    @3
    cI
    @14
    cC
    @0
    @9
    @17
    @3
    eqid
    #
    @9
    eqid
    #
    hdmap12b.i
    lmodvnegid
    syl2anc
    wph
    @12
    @9
    wceq
    @11
    cU
    c0g
    cfv
    #
    wceq
    #
    wph
    cU
    clmod
    wcel
    #
    cT
    cV
    wcel
    #
    @22
    wph
    cU
    cH
    cK
    cW
    hdmap12b.h
    hdmap12b.u
    hdmap12b.k
    dvhlmod
    #
    hdmap12b.x
    @10
    cM
    cV
    cU
    cT
    @21
    hdmap12b.v
    @10
    eqid
    #
    @21
    eqid
    #
    hdmap12b.m
    lmodvnegid
    syl2anc
    wph
    cC
    @9
    cS
    @11
    cU
    cH
    cK
    cV
    cW
    @21
    hdmap12b.h
    hdmap12b.u
    hdmap12b.v
    @27
    hdmap12b.c
    @20
    hdmap12b.s
    hdmap12b.k
    wph
    @23
    @24
    @1
    cV
    wcel
    #
    @11
    cV
    wcel
    @25
    hdmap12b.x
    wph
    @23
    @24
    @28
    @25
    hdmap12b.x
    cM
    cV
    cU
    cT
    hdmap12b.v
    hdmap12b.m
    lmodvnegcl
    syl2anc
    #
    @10
    cV
    cU
    cT
    @1
    hdmap12b.v
    @26
    lmodvacl
    syl3anc
    hdmapeq0
    mpbird
    wph
    cC
    @10
    @3
    cS
    cU
    cH
    cK
    cV
    cW
    cT
    @1
    hdmap12b.h
    hdmap12b.u
    hdmap12b.v
    @26
    hdmap12b.c
    @19
    hdmap12b.s
    hdmap12b.k
    hdmap12b.x
    @29
    hdmapadd
    3eqtr2rd
    wph
    @13
    @2
    @14
    wcel
    @5
    @14
    wcel
    #
    @15
    @7
    @8
    wb
    @16
    wph
    cC
    @14
    cS
    @1
    cU
    cH
    cK
    cV
    cW
    hdmap12b.h
    hdmap12b.u
    hdmap12b.v
    hdmap12b.c
    @17
    hdmap12b.s
    hdmap12b.k
    @29
    hdmapcl
    wph
    @13
    @15
    @30
    @16
    @18
    cI
    @14
    cC
    @0
    @17
    hdmap12b.i
    lmodvnegcl
    syl2anc
    @18
    @3
    @14
    cC
    @2
    @5
    @0
    @17
    @19
    lmodlcan
    syl13anc
    mpbid
end
