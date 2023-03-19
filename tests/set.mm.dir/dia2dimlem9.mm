include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "csubg.mm"
include "chlt.mm"
include "clvec.mm"
include "clmod.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "lsssssubg.mm"
include "4syl.mm"
include "cbs.mm"
include "wbr.mm"
include "simpld.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simprd.mm"
include "dialss.mm"
include "syl12anc.mm"
include "sseldd.mm"
include "lsmub1.mm"
include "syl2anc.mm"
include "adantr.mm"
include "dia1dimid.mm"
include "fveq2.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "lsmub2.mm"
include "wne.mm"
include "simprl.mm"
include "simprr.mm"
include "dia2dimlem8.mm"
include "pm2.61da2ne.mm"

theorem dia2dimlem9
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
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
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y
  assume dia2dimlem9.l: |- .<_ = ( le ` K )
  assume dia2dimlem9.j: |- .\/ = ( join ` K )
  assume dia2dimlem9.m: |- ./\ = ( meet ` K )
  assume dia2dimlem9.a: |- A = ( Atoms ` K )
  assume dia2dimlem9.h: |- H = ( LHyp ` K )
  assume dia2dimlem9.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem9.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem9.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem9.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem9.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem9.n: |- N = ( LSpan ` Y )
  assume dia2dimlem9.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem9.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem9.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem9.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem9.f: |- ( ph -> F e. T )
  assume dia2dimlem9.rf: |- ( ph -> ( R ` F ) .<_ ( U .\/ V ) )
  assume dia2dimlem9.uv: |- ( ph -> U =/= V )


  assert |- ( ph -> F e. ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cF
    cU
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
    wcel
    cF
    cR
    cfv
    #
    cU
    @3
    cV
    wph
    @3
    cU
    wceq
    #
    wa
    #
    @0
    @2
    cF
    wph
    @0
    @2
    wss
    #
    @4
    wph
    @0
    cY
    csubg
    cfv
    #
    wcel
    #
    @1
    @7
    wcel
    #
    @6
    wph
    cS
    @7
    @0
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cY
    clvec
    wcel
    cY
    clmod
    wcel
    cS
    @7
    wss
    dia2dimlem9.k
    cY
    cH
    cK
    cW
    dia2dimlem9.h
    dia2dimlem9.y
    dvalvec
    cY
    lveclmod
    cS
    cY
    dia2dimlem9.s
    lsssssubg
    4syl
    #
    wph
    @10
    cU
    cK
    cbs
    cfv
    #
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    @0
    cS
    wcel
    dia2dimlem9.k
    wph
    cU
    cA
    wcel
    #
    @13
    wph
    @15
    @14
    dia2dimlem9.u
    simpld
    cA
    @12
    cU
    cK
    @12
    eqid
    #
    dia2dimlem9.a
    atbase
    syl
    wph
    @15
    @14
    dia2dimlem9.u
    simprd
    @12
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    cU
    @16
    dia2dimlem9.l
    dia2dimlem9.h
    dia2dimlem9.y
    dia2dimlem9.i
    dia2dimlem9.s
    dialss
    syl12anc
    sseldd
    #
    wph
    cS
    @7
    @1
    @11
    wph
    @10
    cV
    @12
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    @1
    cS
    wcel
    dia2dimlem9.k
    wph
    cV
    cA
    wcel
    #
    @18
    wph
    @20
    @19
    dia2dimlem9.v
    simpld
    cA
    @12
    cV
    cK
    @16
    dia2dimlem9.a
    atbase
    syl
    wph
    @20
    @19
    dia2dimlem9.v
    simprd
    @12
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    cV
    @16
    dia2dimlem9.l
    dia2dimlem9.h
    dia2dimlem9.y
    dia2dimlem9.i
    dia2dimlem9.s
    dialss
    syl12anc
    sseldd
    #
    c.po
    @0
    @1
    cY
    dia2dimlem9.pl
    lsmub1
    syl2anc
    adantr
    @5
    cF
    @3
    cI
    cfv
    #
    @0
    wph
    cF
    @22
    wcel
    #
    @4
    wph
    @10
    cF
    cT
    wcel
    #
    @23
    dia2dimlem9.k
    dia2dimlem9.f
    cR
    cT
    cF
    cH
    cI
    cK
    cW
    dia2dimlem9.h
    dia2dimlem9.t
    dia2dimlem9.r
    dia2dimlem9.i
    dia1dimid
    syl2anc
    #
    adantr
    @4
    @22
    @0
    wceq
    wph
    @3
    cU
    cI
    fveq2
    adantl
    eleqtrd
    sseldd
    wph
    @3
    cV
    wceq
    #
    wa
    #
    @1
    @2
    cF
    @27
    @8
    @9
    @1
    @2
    wss
    wph
    @8
    @26
    @17
    adantr
    wph
    @9
    @26
    @21
    adantr
    c.po
    @0
    @1
    cY
    dia2dimlem9.pl
    lsmub2
    syl2anc
    @27
    cF
    @22
    @1
    wph
    @23
    @26
    @25
    adantr
    @26
    @22
    @1
    wceq
    wph
    @3
    cV
    cI
    fveq2
    adantl
    eleqtrd
    sseldd
    wph
    @3
    cU
    wne
    #
    @3
    cV
    wne
    #
    wa
    #
    wa
    cA
    c.po
    cR
    cS
    cT
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cV
    cW
    cY
    dia2dimlem9.l
    dia2dimlem9.j
    dia2dimlem9.m
    dia2dimlem9.a
    dia2dimlem9.h
    dia2dimlem9.t
    dia2dimlem9.r
    dia2dimlem9.y
    dia2dimlem9.s
    dia2dimlem9.pl
    dia2dimlem9.n
    dia2dimlem9.i
    wph
    @10
    @30
    dia2dimlem9.k
    adantr
    wph
    @15
    @14
    wa
    @30
    dia2dimlem9.u
    adantr
    wph
    @20
    @19
    wa
    @30
    dia2dimlem9.v
    adantr
    wph
    @24
    @30
    dia2dimlem9.f
    adantr
    wph
    @3
    cU
    cV
    c.or
    co
    c.le
    wbr
    @30
    dia2dimlem9.rf
    adantr
    wph
    cU
    cV
    wne
    @30
    dia2dimlem9.uv
    adantr
    wph
    @28
    @29
    simprl
    wph
    @28
    @29
    simprr
    dia2dimlem8
    pm2.61da2ne
end
