include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wbr.mm"
include "csn.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "dia1dim2.mm"
include "syl2anc.mm"
include "clvec.mm"
include "clmod.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "3syl.mm"
include "cbs.mm"
include "simpld.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simprd.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "dialss.mm"
include "syl12anc.mm"
include "lspsnel5a.mm"
include "eqsstrd.mm"
include "trlcl.mm"
include "trlle.mm"
include "diaord.mm"
include "syl122anc.mm"
include "mpbid.mm"

theorem dia2dimlem10
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y
  assume dia2dimlem10.l: |- .<_ = ( le ` K )
  assume dia2dimlem10.j: |- .\/ = ( join ` K )
  assume dia2dimlem10.a: |- A = ( Atoms ` K )
  assume dia2dimlem10.h: |- H = ( LHyp ` K )
  assume dia2dimlem10.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem10.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem10.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem10.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem10.n: |- N = ( LSpan ` Y )
  assume dia2dimlem10.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem10.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem10.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem10.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem10.f: |- ( ph -> F e. T )
  assume dia2dimlem10.fe: |- ( ph -> F e. ( I ` ( U .\/ V ) ) )


  assert |- ( ph -> ( R ` F ) .<_ ( U .\/ V ) )

  proof
    wph
    cF
    cR
    cfv
    #
    cI
    cfv
    #
    cU
    cV
    c.or
    co
    #
    cI
    cfv
    #
    wss
    #
    @0
    @2
    c.le
    wbr
    #
    wph
    @1
    cF
    csn
    cN
    cfv
    #
    @3
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
    cF
    cT
    wcel
    #
    @1
    @6
    wceq
    dia2dimlem10.k
    dia2dimlem10.f
    cR
    cT
    cY
    cF
    cH
    cI
    cK
    cN
    cW
    dia2dimlem10.h
    dia2dimlem10.t
    dia2dimlem10.r
    dia2dimlem10.y
    dia2dimlem10.i
    dia2dimlem10.n
    dia1dim2
    syl2anc
    wph
    cS
    @3
    cN
    cY
    cF
    dia2dimlem10.s
    dia2dimlem10.n
    wph
    @9
    cY
    clvec
    wcel
    cY
    clmod
    wcel
    dia2dimlem10.k
    cY
    cH
    cK
    cW
    dia2dimlem10.h
    dia2dimlem10.y
    dvalvec
    cY
    lveclmod
    3syl
    wph
    @9
    @2
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    cW
    c.le
    wbr
    #
    @3
    cS
    wcel
    dia2dimlem10.k
    wph
    @7
    cU
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    @12
    wph
    @7
    @8
    dia2dimlem10.k
    simpld
    #
    wph
    @14
    cU
    cW
    c.le
    wbr
    #
    dia2dimlem10.u
    simpld
    #
    wph
    @15
    cV
    cW
    c.le
    wbr
    #
    dia2dimlem10.v
    simpld
    #
    cA
    @11
    c.or
    cK
    cU
    cV
    @11
    eqid
    #
    dia2dimlem10.j
    dia2dimlem10.a
    hlatjcl
    syl3anc
    #
    wph
    @17
    @19
    @13
    wph
    @14
    @17
    dia2dimlem10.u
    simprd
    wph
    @15
    @19
    dia2dimlem10.v
    simprd
    wph
    cK
    clat
    wcel
    #
    cU
    @11
    wcel
    #
    cV
    @11
    wcel
    #
    cW
    @11
    wcel
    #
    @17
    @19
    wa
    @13
    wb
    wph
    @7
    @23
    @16
    cK
    hllat
    syl
    wph
    @14
    @24
    @18
    cA
    @11
    cU
    cK
    @21
    dia2dimlem10.a
    atbase
    syl
    wph
    @15
    @25
    @20
    cA
    @11
    cV
    cK
    @21
    dia2dimlem10.a
    atbase
    syl
    wph
    @8
    @26
    wph
    @7
    @8
    dia2dimlem10.k
    simprd
    @11
    cH
    cK
    cW
    @21
    dia2dimlem10.h
    lhpbase
    syl
    @11
    c.or
    cK
    c.le
    cU
    cV
    cW
    @21
    dia2dimlem10.l
    dia2dimlem10.j
    latjle12
    syl13anc
    mpbi2and
    #
    @11
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    @2
    @21
    dia2dimlem10.l
    dia2dimlem10.h
    dia2dimlem10.y
    dia2dimlem10.i
    dia2dimlem10.s
    dialss
    syl12anc
    dia2dimlem10.fe
    lspsnel5a
    eqsstrd
    wph
    @9
    @0
    @11
    wcel
    #
    @0
    cW
    c.le
    wbr
    #
    @12
    @13
    @4
    @5
    wb
    dia2dimlem10.k
    wph
    @9
    @10
    @28
    dia2dimlem10.k
    dia2dimlem10.f
    @11
    cR
    cT
    cF
    cH
    cK
    cW
    @21
    dia2dimlem10.h
    dia2dimlem10.t
    dia2dimlem10.r
    trlcl
    syl2anc
    wph
    @9
    @10
    @29
    dia2dimlem10.k
    dia2dimlem10.f
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    dia2dimlem10.l
    dia2dimlem10.h
    dia2dimlem10.t
    dia2dimlem10.r
    trlle
    syl2anc
    @22
    @27
    @11
    cH
    cI
    cK
    c.le
    cW
    @0
    @2
    @21
    dia2dimlem10.l
    dia2dimlem10.h
    dia2dimlem10.i
    diaord
    syl122anc
    mpbid
end
