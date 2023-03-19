include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "ccnv.mm"
include "cjn.mm"
include "co.mm"
include "crn.mm"
include "cun.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "clsm.mm"
include "catm.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "dihlspsnat.mm"
include "syl3anc.mm"
include "dihjat.mm"
include "wceq.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dihcnvid2.mm"
include "oveq12d.mm"
include "clmod.mm"
include "wss.mm"
include "dvhlmod.mm"
include "snssd.mm"
include "lsmsp2.mm"
include "3eqtrrd.mm"
include "syl5eq.mm"
include "cbs.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "syl.mm"
include "dihcnvcl.mm"
include "latjcl.mm"
include "dihcl.mm"
include "eqeltrd.mm"

theorem dihprrnlem2
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume dihprrn.h: |- H = ( LHyp ` K )
  assume dihprrn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihprrn.v: |- V = ( Base ` U )
  assume dihprrn.n: |- N = ( LSpan ` U )
  assume dihprrn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihprrn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihprrn.x: |- ( ph -> X e. V )
  assume dihprrn.y: |- ( ph -> Y e. V )
  assume dihprrnlem2.o: |- .0. = ( 0g ` U )
  assume dihprrnlem2.xz: |- ( ph -> X =/= .0. )
  assume dihprrnlem2.yz: |- ( ph -> Y =/= .0. )


  assert |- ( ph -> ( N ` { X , Y } ) e. ran I )

  proof
    wph
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    cX
    csn
    #
    cN
    cfv
    #
    cI
    ccnv
    #
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    @4
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cI
    cfv
    #
    cI
    crn
    #
    wph
    @1
    @2
    @6
    cun
    #
    cN
    cfv
    #
    @11
    @0
    @13
    cN
    cX
    cY
    df-pr
    fveq2i
    wph
    @11
    @5
    cI
    cfv
    #
    @8
    cI
    cfv
    #
    cU
    clsm
    cfv
    #
    co
    @3
    @7
    @17
    co
    #
    @14
    wph
    cK
    catm
    cfv
    #
    @5
    @17
    @8
    cU
    cH
    cI
    @9
    cK
    cW
    dihprrn.h
    @9
    eqid
    #
    @19
    eqid
    #
    dihprrn.u
    @17
    eqid
    #
    dihprrn.i
    dihprrn.k
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
    cX
    cV
    wcel
    #
    cX
    c.0
    wne
    @5
    @19
    wcel
    dihprrn.k
    dihprrn.x
    dihprrnlem2.xz
    @19
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    c.0
    @21
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrnlem2.o
    dihprrn.n
    dihprrn.i
    dihlspsnat
    syl3anc
    wph
    @25
    cY
    cV
    wcel
    #
    cY
    c.0
    wne
    @8
    @19
    wcel
    dihprrn.k
    dihprrn.y
    dihprrnlem2.yz
    @19
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cY
    c.0
    @21
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrnlem2.o
    dihprrn.n
    dihprrn.i
    dihlspsnat
    syl3anc
    dihjat
    wph
    @15
    @3
    @16
    @7
    @17
    wph
    @25
    @3
    @12
    wcel
    #
    @15
    @3
    wceq
    dihprrn.k
    wph
    @25
    @26
    @28
    dihprrn.k
    dihprrn.x
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrn.n
    dihprrn.i
    dihlsprn
    syl2anc
    #
    cH
    cI
    cK
    cW
    @3
    dihprrn.h
    dihprrn.i
    dihcnvid2
    syl2anc
    wph
    @25
    @7
    @12
    wcel
    #
    @16
    @7
    wceq
    dihprrn.k
    wph
    @25
    @27
    @30
    dihprrn.k
    dihprrn.y
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cY
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrn.n
    dihprrn.i
    dihlsprn
    syl2anc
    #
    cH
    cI
    cK
    cW
    @7
    dihprrn.h
    dihprrn.i
    dihcnvid2
    syl2anc
    oveq12d
    wph
    cU
    clmod
    wcel
    @2
    cV
    wss
    @6
    cV
    wss
    @18
    @14
    wceq
    wph
    cU
    cH
    cK
    cW
    dihprrn.h
    dihprrn.u
    dihprrn.k
    dvhlmod
    wph
    cX
    cV
    dihprrn.x
    snssd
    wph
    cY
    cV
    dihprrn.y
    snssd
    @17
    @2
    @6
    cN
    cV
    cU
    dihprrn.v
    dihprrn.n
    @22
    lsmsp2
    syl3anc
    3eqtrrd
    syl5eq
    wph
    @25
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    @12
    wcel
    dihprrn.k
    wph
    cK
    clat
    wcel
    #
    @5
    @32
    wcel
    #
    @8
    @32
    wcel
    #
    @33
    wph
    @23
    @34
    wph
    @23
    @24
    dihprrn.k
    simpld
    cK
    hllat
    syl
    wph
    @25
    @28
    @35
    dihprrn.k
    @29
    @32
    cH
    cI
    cK
    cW
    @3
    @32
    eqid
    #
    dihprrn.h
    dihprrn.i
    dihcnvcl
    syl2anc
    wph
    @25
    @30
    @36
    dihprrn.k
    @31
    @32
    cH
    cI
    cK
    cW
    @7
    @37
    dihprrn.h
    dihprrn.i
    dihcnvcl
    syl2anc
    @32
    @9
    cK
    @5
    @8
    @37
    @20
    latjcl
    syl3anc
    @32
    cH
    cI
    cK
    cW
    @10
    @37
    dihprrn.h
    dihprrn.i
    dihcl
    syl2anc
    eqeltrd
end
