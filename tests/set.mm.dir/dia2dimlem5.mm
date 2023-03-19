include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "ccom.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "dvavadd.mm"
include "syl12anc.mm"
include "wne.mm"
include "simpld.mm"
include "dia2dimlem4.mm"
include "eqtr2d.mm"
include "csubg.mm"
include "clmod.mm"
include "wss.mm"
include "clvec.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "3syl.mm"
include "lsssssubg.mm"
include "syl.mm"
include "cbs.mm"
include "wbr.mm"
include "atbase.mm"
include "simprd.mm"
include "dialss.mm"
include "sseldd.mm"
include "csn.mm"
include "dia1dim2.mm"
include "syl2anc.mm"
include "dia2dimlem3.mm"
include "fveq2d.mm"
include "eqss.mm"
include "sylib.mm"
include "eqsstr3d.mm"
include "dvavbase.mm"
include "eleqtrrd.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "dia2dimlem2.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "cabl.mm"
include "lmodabl.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "eleqtrd.mm"

theorem dia2dimlem5
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y
  assume dia2dimlem5.l: |- .<_ = ( le ` K )
  assume dia2dimlem5.j: |- .\/ = ( join ` K )
  assume dia2dimlem5.m: |- ./\ = ( meet ` K )
  assume dia2dimlem5.a: |- A = ( Atoms ` K )
  assume dia2dimlem5.h: |- H = ( LHyp ` K )
  assume dia2dimlem5.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem5.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem5.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem5.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem5.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem5.n: |- N = ( LSpan ` Y )
  assume dia2dimlem5.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem5.q: |- Q = ( ( P .\/ U ) ./\ ( ( F ` P ) .\/ V ) )
  assume dia2dimlem5.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem5.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem5.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem5.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dia2dimlem5.f: |- ( ph -> ( F e. T /\ ( F ` P ) =/= P ) )
  assume dia2dimlem5.rf: |- ( ph -> ( R ` F ) .<_ ( U .\/ V ) )
  assume dia2dimlem5.uv: |- ( ph -> U =/= V )
  assume dia2dimlem5.ru: |- ( ph -> ( R ` F ) =/= U )
  assume dia2dimlem5.rv: |- ( ph -> ( R ` F ) =/= V )
  assume dia2dimlem5.g: |- ( ph -> G e. T )
  assume dia2dimlem5.gv: |- ( ph -> ( G ` P ) = Q )
  assume dia2dimlem5.d: |- ( ph -> D e. T )
  assume dia2dimlem5.dv: |- ( ph -> ( D ` Q ) = ( F ` P ) )


  assert |- ( ph -> F e. ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cF
    cV
    cI
    cfv
    #
    cU
    cI
    cfv
    #
    c.po
    co
    #
    @1
    @0
    c.po
    co
    #
    wph
    cF
    cD
    cG
    cY
    cplusg
    cfv
    #
    co
    #
    @2
    wph
    @5
    cD
    cG
    ccom
    #
    cF
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cD
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    @5
    @6
    wceq
    dia2dimlem5.k
    dia2dimlem5.d
    dia2dimlem5.g
    @4
    cT
    cY
    cD
    cG
    cH
    cK
    chlt
    cW
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.y
    @4
    eqid
    #
    dvavadd
    syl12anc
    wph
    cA
    cD
    cP
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    dia2dimlem5.l
    dia2dimlem5.a
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.k
    dia2dimlem5.p
    wph
    cF
    cT
    wcel
    cP
    cF
    cfv
    cP
    wne
    dia2dimlem5.f
    simpld
    dia2dimlem5.g
    dia2dimlem5.gv
    dia2dimlem5.d
    dia2dimlem5.dv
    dia2dimlem4
    eqtr2d
    wph
    @0
    cY
    csubg
    cfv
    #
    wcel
    #
    @1
    @11
    wcel
    #
    cD
    @0
    wcel
    #
    cG
    @1
    wcel
    #
    @5
    @2
    wcel
    wph
    cS
    @11
    @0
    wph
    cY
    clmod
    wcel
    #
    cS
    @11
    wss
    wph
    @7
    cY
    clvec
    wcel
    @16
    dia2dimlem5.k
    cY
    cH
    cK
    cW
    dia2dimlem5.h
    dia2dimlem5.y
    dvalvec
    cY
    lveclmod
    3syl
    #
    cS
    cY
    dia2dimlem5.s
    lsssssubg
    syl
    #
    wph
    @7
    cV
    cK
    cbs
    cfv
    #
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    @0
    cS
    wcel
    dia2dimlem5.k
    wph
    cV
    cA
    wcel
    #
    @20
    wph
    @22
    @21
    dia2dimlem5.v
    simpld
    cA
    @19
    cV
    cK
    @19
    eqid
    #
    dia2dimlem5.a
    atbase
    syl
    wph
    @22
    @21
    dia2dimlem5.v
    simprd
    @19
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    cV
    @23
    dia2dimlem5.l
    dia2dimlem5.h
    dia2dimlem5.y
    dia2dimlem5.i
    dia2dimlem5.s
    dialss
    syl12anc
    #
    sseldd
    #
    wph
    cS
    @11
    @1
    @18
    wph
    @7
    cU
    @19
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    @1
    cS
    wcel
    dia2dimlem5.k
    wph
    cU
    cA
    wcel
    #
    @26
    wph
    @28
    @27
    dia2dimlem5.u
    simpld
    cA
    @19
    cU
    cK
    @23
    dia2dimlem5.a
    atbase
    syl
    wph
    @28
    @27
    dia2dimlem5.u
    simprd
    @19
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    cU
    @23
    dia2dimlem5.l
    dia2dimlem5.h
    dia2dimlem5.y
    dia2dimlem5.i
    dia2dimlem5.s
    dialss
    syl12anc
    #
    sseldd
    #
    wph
    @14
    cD
    csn
    cN
    cfv
    #
    @0
    wss
    wph
    @31
    cD
    cR
    cfv
    #
    cI
    cfv
    #
    @0
    wph
    @7
    @8
    @33
    @31
    wceq
    dia2dimlem5.k
    dia2dimlem5.d
    cR
    cT
    cY
    cD
    cH
    cI
    cK
    cN
    cW
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.r
    dia2dimlem5.y
    dia2dimlem5.i
    dia2dimlem5.n
    dia1dim2
    syl2anc
    wph
    @33
    @0
    wss
    #
    @0
    @33
    wss
    #
    wph
    @33
    @0
    wceq
    @34
    @35
    wa
    wph
    @32
    cV
    cI
    wph
    cA
    cD
    cP
    cQ
    cR
    cT
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    dia2dimlem5.l
    dia2dimlem5.j
    dia2dimlem5.m
    dia2dimlem5.a
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.r
    dia2dimlem5.q
    dia2dimlem5.k
    dia2dimlem5.u
    dia2dimlem5.v
    dia2dimlem5.p
    dia2dimlem5.f
    dia2dimlem5.rf
    dia2dimlem5.uv
    dia2dimlem5.ru
    dia2dimlem5.rv
    dia2dimlem5.d
    dia2dimlem5.dv
    dia2dimlem3
    fveq2d
    @33
    @0
    eqss
    sylib
    simpld
    eqsstr3d
    wph
    cS
    @0
    cN
    cY
    cbs
    cfv
    #
    cY
    cD
    @36
    eqid
    #
    dia2dimlem5.s
    dia2dimlem5.n
    @17
    @24
    wph
    cD
    cT
    @36
    dia2dimlem5.d
    wph
    @7
    @36
    cT
    wceq
    dia2dimlem5.k
    cT
    cY
    cH
    cK
    @36
    cW
    chlt
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.y
    @37
    dvavbase
    syl
    #
    eleqtrrd
    lspsnel5
    mpbird
    wph
    @15
    cG
    csn
    cN
    cfv
    #
    @1
    wss
    wph
    @39
    cG
    cR
    cfv
    #
    cI
    cfv
    #
    @1
    wph
    @7
    @9
    @41
    @39
    wceq
    dia2dimlem5.k
    dia2dimlem5.g
    cR
    cT
    cY
    cG
    cH
    cI
    cK
    cN
    cW
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.r
    dia2dimlem5.y
    dia2dimlem5.i
    dia2dimlem5.n
    dia1dim2
    syl2anc
    wph
    @41
    @1
    wss
    #
    @1
    @41
    wss
    #
    wph
    @41
    @1
    wceq
    @42
    @43
    wa
    wph
    @40
    cU
    cI
    wph
    cA
    cP
    cQ
    cR
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    dia2dimlem5.l
    dia2dimlem5.j
    dia2dimlem5.m
    dia2dimlem5.a
    dia2dimlem5.h
    dia2dimlem5.t
    dia2dimlem5.r
    dia2dimlem5.q
    dia2dimlem5.k
    dia2dimlem5.u
    dia2dimlem5.v
    dia2dimlem5.p
    dia2dimlem5.f
    dia2dimlem5.rf
    dia2dimlem5.rv
    dia2dimlem5.g
    dia2dimlem5.gv
    dia2dimlem2
    fveq2d
    @41
    @1
    eqss
    sylib
    simpld
    eqsstr3d
    wph
    cS
    @1
    cN
    @36
    cY
    cG
    @37
    dia2dimlem5.s
    dia2dimlem5.n
    @17
    @29
    wph
    cG
    cT
    @36
    dia2dimlem5.g
    @38
    eleqtrrd
    lspsnel5
    mpbird
    @4
    c.po
    @0
    @1
    cY
    cD
    cG
    @10
    dia2dimlem5.pl
    lsmelvali
    syl22anc
    eqeltrd
    wph
    cY
    cabl
    wcel
    #
    @12
    @13
    @2
    @3
    wceq
    wph
    @16
    @44
    @17
    cY
    lmodabl
    syl
    @25
    @30
    c.po
    @0
    @1
    cY
    dia2dimlem5.pl
    lsmcom
    syl3anc
    eleqtrd
end
