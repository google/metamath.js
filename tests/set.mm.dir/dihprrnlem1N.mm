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
include "cbs.mm"
include "eqid.mm"
include "wcel.mm"
include "wbr.mm"
include "chlt.mm"
include "wa.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dihcnvcl.mm"
include "jca.mm"
include "wn.mm"
include "wne.mm"
include "dihlspsnat.mm"
include "syl3anc.mm"
include "dihjatc.mm"
include "wceq.mm"
include "dihcnvid2.mm"
include "oveq12d.mm"
include "clmod.mm"
include "wss.mm"
include "dvhlmod.mm"
include "snssd.mm"
include "lsmsp2.mm"
include "3eqtrrd.mm"
include "syl5eq.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "syl.mm"
include "latjcl.mm"
include "dihcl.mm"
include "eqeltrd.mm"

theorem dihprrnlem1N
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
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
  assume dihprrnlem1.l: |- .<_ = ( le ` K )
  assume dihprrnlem1.o: |- .0. = ( 0g ` U )
  assume dihprrnlem1.nz: |- ( ph -> Y =/= .0. )
  assume dihprrnlem1.x: |- ( ph -> ( `' I ` ( N ` { X } ) ) .<_ W )
  assume dihprrnlem1.y: |- ( ph -> -. ( `' I ` ( N ` { Y } ) ) .<_ W )


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
    cK
    cbs
    cfv
    #
    @8
    @17
    cU
    cH
    cI
    @9
    cK
    c.le
    cW
    @5
    @20
    eqid
    #
    dihprrnlem1.l
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
    @5
    @20
    wcel
    #
    @5
    cW
    c.le
    wbr
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
    @3
    @12
    wcel
    #
    @25
    dihprrn.k
    wph
    @28
    cX
    cV
    wcel
    @29
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
    @20
    cH
    cI
    cK
    cW
    @3
    @21
    dihprrn.h
    dihprrn.i
    dihcnvcl
    syl2anc
    #
    dihprrnlem1.x
    jca
    wph
    @8
    @19
    wcel
    #
    @8
    cW
    c.le
    wbr
    wn
    wph
    @28
    cY
    cV
    wcel
    #
    cY
    c.0
    wne
    @32
    dihprrn.k
    dihprrn.y
    dihprrnlem1.nz
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
    @23
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrnlem1.o
    dihprrn.n
    dihprrn.i
    dihlspsnat
    syl3anc
    dihprrnlem1.y
    jca
    dihjatc
    wph
    @15
    @3
    @16
    @7
    @17
    wph
    @28
    @29
    @15
    @3
    wceq
    dihprrn.k
    @30
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
    @28
    @7
    @12
    wcel
    #
    @16
    @7
    wceq
    dihprrn.k
    wph
    @28
    @33
    @34
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
    @24
    lsmsp2
    syl3anc
    3eqtrrd
    syl5eq
    wph
    @28
    @10
    @20
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
    @25
    @8
    @20
    wcel
    #
    @36
    wph
    @26
    @37
    wph
    @26
    @27
    dihprrn.k
    simpld
    cK
    hllat
    syl
    @31
    wph
    @28
    @34
    @38
    dihprrn.k
    @35
    @20
    cH
    cI
    cK
    cW
    @7
    @21
    dihprrn.h
    dihprrn.i
    dihcnvcl
    syl2anc
    @20
    @9
    cK
    @5
    @8
    @21
    @22
    latjcl
    syl3anc
    @20
    cH
    cI
    cK
    cW
    @10
    @21
    dihprrn.h
    dihprrn.i
    dihcl
    syl2anc
    eqeltrd
end
