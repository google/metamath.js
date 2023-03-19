include "co.mm"
include "cfv.mm"
include "ccnv.mm"
include "wss.mm"
include "csubg.mm"
include "wcel.mm"
include "clss.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "mapdcl2.mm"
include "sseldd.mm"
include "lsmub1.mm"
include "syl2anc.mm"
include "mapdcl.mm"
include "mapdlsmcl.mm"
include "mapdcnvid2.mm"
include "sseqtr4d.mm"
include "mapdcnvcl.mm"
include "mapdord.mm"
include "mpbid.mm"
include "lsmub2.mm"
include "wa.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lsmlub.mm"
include "syl3anc.mm"
include "mpbi2and.mm"
include "lsmcl.mm"
include "mpbird.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem mapdlsm
  let wph: wff ph
  let cC: class C
  let c.pb: class .+b
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdlsm.h: |- H = ( LHyp ` K )
  assume mapdlsm.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdlsm.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdlsm.s: |- S = ( LSubSp ` U )
  assume mapdlsm.p: |- .(+) = ( LSSum ` U )
  assume mapdlsm.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdlsm.q: |- .+b = ( LSSum ` C )
  assume mapdlsm.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdlsm.x: |- ( ph -> X e. S )
  assume mapdlsm.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( M ` ( X .(+) Y ) ) = ( ( M ` X ) .+b ( M ` Y ) ) )

  proof
    wph
    cX
    cY
    c.po
    co
    #
    cM
    cfv
    #
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    c.pb
    co
    #
    wph
    @1
    @4
    cM
    ccnv
    cfv
    #
    cM
    cfv
    #
    @4
    wph
    @1
    @6
    wss
    @0
    @5
    wss
    #
    wph
    cX
    @5
    wss
    #
    cY
    @5
    wss
    #
    @7
    wph
    @2
    @6
    wss
    @8
    wph
    @2
    @4
    @6
    wph
    @2
    cC
    csubg
    cfv
    #
    wcel
    #
    @3
    @10
    wcel
    #
    @2
    @4
    wss
    wph
    cC
    clss
    cfv
    #
    @10
    @2
    wph
    cC
    clmod
    wcel
    @13
    @10
    wss
    wph
    cC
    cH
    cK
    cW
    mapdlsm.h
    mapdlsm.c
    mapdlsm.k
    lcdlmod
    @13
    cC
    @13
    eqid
    #
    lsssssubg
    syl
    #
    wph
    cC
    cX
    cS
    @13
    cU
    cH
    cK
    cM
    cW
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.s
    mapdlsm.c
    @14
    mapdlsm.k
    mapdlsm.x
    mapdcl2
    sseldd
    #
    wph
    @13
    @10
    @3
    @15
    wph
    cC
    cY
    cS
    @13
    cU
    cH
    cK
    cM
    cW
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.s
    mapdlsm.c
    @14
    mapdlsm.k
    mapdlsm.y
    mapdcl2
    sseldd
    #
    c.pb
    @2
    @3
    cC
    mapdlsm.q
    lsmub1
    syl2anc
    wph
    cH
    cK
    cM
    cW
    @4
    mapdlsm.h
    mapdlsm.m
    mapdlsm.k
    wph
    cC
    c.pb
    cU
    cH
    cK
    cM
    cW
    @2
    @3
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.c
    mapdlsm.q
    mapdlsm.k
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cX
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.s
    mapdlsm.k
    mapdlsm.x
    mapdcl
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cY
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.s
    mapdlsm.k
    mapdlsm.y
    mapdcl
    mapdlsmcl
    #
    mapdcnvid2
    #
    sseqtr4d
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cX
    @5
    mapdlsm.h
    mapdlsm.u
    mapdlsm.s
    mapdlsm.m
    mapdlsm.k
    mapdlsm.x
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @4
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.s
    mapdlsm.k
    @18
    mapdcnvcl
    #
    mapdord
    mpbid
    wph
    @3
    @6
    wss
    @9
    wph
    @3
    @4
    @6
    wph
    @11
    @12
    @3
    @4
    wss
    @16
    @17
    c.pb
    @2
    @3
    cC
    mapdlsm.q
    lsmub2
    syl2anc
    @19
    sseqtr4d
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cY
    @5
    mapdlsm.h
    mapdlsm.u
    mapdlsm.s
    mapdlsm.m
    mapdlsm.k
    mapdlsm.y
    @20
    mapdord
    mpbid
    wph
    cX
    cU
    csubg
    cfv
    #
    wcel
    #
    cY
    @21
    wcel
    #
    @5
    @21
    wcel
    @8
    @9
    wa
    @7
    wb
    wph
    cS
    @21
    cX
    wph
    cU
    clmod
    wcel
    #
    cS
    @21
    wss
    wph
    cU
    cH
    cK
    cW
    mapdlsm.h
    mapdlsm.u
    mapdlsm.k
    dvhlmod
    #
    cS
    cU
    mapdlsm.s
    lsssssubg
    syl
    #
    mapdlsm.x
    sseldd
    #
    wph
    cS
    @21
    cY
    @26
    mapdlsm.y
    sseldd
    #
    wph
    cS
    @21
    @5
    @26
    @20
    sseldd
    c.po
    cX
    cY
    @5
    cU
    mapdlsm.p
    lsmlub
    syl3anc
    mpbi2and
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @0
    @5
    mapdlsm.h
    mapdlsm.u
    mapdlsm.s
    mapdlsm.m
    mapdlsm.k
    wph
    @24
    cX
    cS
    wcel
    cY
    cS
    wcel
    @0
    cS
    wcel
    @25
    mapdlsm.x
    mapdlsm.y
    c.po
    cS
    cX
    cY
    cU
    mapdlsm.s
    mapdlsm.p
    lsmcl
    syl3anc
    #
    @20
    mapdord
    mpbird
    @19
    sseqtrd
    wph
    @2
    @1
    wss
    #
    @3
    @1
    wss
    #
    @4
    @1
    wss
    #
    wph
    @30
    cX
    @0
    wss
    #
    wph
    @22
    @23
    @33
    @27
    @28
    c.po
    cX
    cY
    cU
    mapdlsm.p
    lsmub1
    syl2anc
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cX
    @0
    mapdlsm.h
    mapdlsm.u
    mapdlsm.s
    mapdlsm.m
    mapdlsm.k
    mapdlsm.x
    @29
    mapdord
    mpbird
    wph
    @31
    cY
    @0
    wss
    #
    wph
    @22
    @23
    @34
    @27
    @28
    c.po
    cX
    cY
    cU
    mapdlsm.p
    lsmub2
    syl2anc
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cY
    @0
    mapdlsm.h
    mapdlsm.u
    mapdlsm.s
    mapdlsm.m
    mapdlsm.k
    mapdlsm.y
    @29
    mapdord
    mpbird
    wph
    @11
    @12
    @1
    @10
    wcel
    @30
    @31
    wa
    @32
    wb
    @16
    @17
    wph
    @13
    @10
    @1
    @15
    wph
    cC
    @0
    cS
    @13
    cU
    cH
    cK
    cM
    cW
    mapdlsm.h
    mapdlsm.m
    mapdlsm.u
    mapdlsm.s
    mapdlsm.c
    @14
    mapdlsm.k
    @29
    mapdcl2
    sseldd
    c.pb
    @2
    @3
    @1
    cC
    mapdlsm.q
    lsmlub
    syl3anc
    mpbi2and
    eqssd
end
