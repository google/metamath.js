include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "chlt.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "eqid.mm"
include "ltrnideq.mm"
include "syl3anc.mm"
include "wi.mm"
include "c0g.mm"
include "dva0g.mm"
include "syl.mm"
include "clmod.mm"
include "clvec.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "3syl.mm"
include "simpld.mm"
include "atbase.mm"
include "simprd.mm"
include "dialss.mm"
include "syl12anc.mm"
include "lsmcl.mm"
include "lss0cl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "eleq1a.mm"
include "sylbird.mm"
include "imp.mm"
include "wne.mm"
include "adantr.mm"
include "anim1i.mm"
include "dia2dimlem6.mm"
include "pm2.61dane.mm"

theorem dia2dimlem7
  let wph: wff ph
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
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
  assume dia2dimlem7.l: |- .<_ = ( le ` K )
  assume dia2dimlem7.j: |- .\/ = ( join ` K )
  assume dia2dimlem7.m: |- ./\ = ( meet ` K )
  assume dia2dimlem7.a: |- A = ( Atoms ` K )
  assume dia2dimlem7.h: |- H = ( LHyp ` K )
  assume dia2dimlem7.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem7.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem7.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem7.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem7.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem7.n: |- N = ( LSpan ` Y )
  assume dia2dimlem7.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem7.q: |- Q = ( ( P .\/ U ) ./\ ( ( F ` P ) .\/ V ) )
  assume dia2dimlem7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem7.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem7.v: |- ( ph -> ( V e. A /\ V .<_ W ) )
  assume dia2dimlem7.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dia2dimlem7.f: |- ( ph -> F e. T )
  assume dia2dimlem7.rf: |- ( ph -> ( R ` F ) .<_ ( U .\/ V ) )
  assume dia2dimlem7.uv: |- ( ph -> U =/= V )
  assume dia2dimlem7.ru: |- ( ph -> ( R ` F ) =/= U )
  assume dia2dimlem7.rv: |- ( ph -> ( R ` F ) =/= V )


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
    #
    cP
    cF
    cfv
    #
    cP
    wph
    @4
    cP
    wceq
    #
    @3
    wph
    @5
    cF
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    wceq
    #
    @3
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @8
    @5
    wb
    dia2dimlem7.k
    dia2dimlem7.f
    dia2dimlem7.p
    cA
    @6
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    @6
    eqid
    #
    dia2dimlem7.l
    dia2dimlem7.a
    dia2dimlem7.h
    dia2dimlem7.t
    ltrnideq
    syl3anc
    wph
    @7
    @2
    wcel
    @8
    @3
    wi
    wph
    cY
    c0g
    cfv
    #
    @7
    @2
    wph
    @9
    @13
    @7
    wceq
    dia2dimlem7.k
    @6
    cT
    cY
    cH
    cK
    cW
    @13
    @12
    dia2dimlem7.h
    dia2dimlem7.t
    dia2dimlem7.y
    @13
    eqid
    #
    dva0g
    syl
    wph
    cY
    clmod
    wcel
    #
    @2
    cS
    wcel
    #
    @13
    @2
    wcel
    wph
    @9
    cY
    clvec
    wcel
    @15
    dia2dimlem7.k
    cY
    cH
    cK
    cW
    dia2dimlem7.h
    dia2dimlem7.y
    dvalvec
    cY
    lveclmod
    3syl
    #
    wph
    @15
    @0
    cS
    wcel
    #
    @1
    cS
    wcel
    #
    @16
    @17
    wph
    @9
    cU
    @6
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    @18
    dia2dimlem7.k
    wph
    cU
    cA
    wcel
    #
    @20
    wph
    @22
    @21
    dia2dimlem7.u
    simpld
    cA
    @6
    cU
    cK
    @12
    dia2dimlem7.a
    atbase
    syl
    wph
    @22
    @21
    dia2dimlem7.u
    simprd
    @6
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    cU
    @12
    dia2dimlem7.l
    dia2dimlem7.h
    dia2dimlem7.y
    dia2dimlem7.i
    dia2dimlem7.s
    dialss
    syl12anc
    wph
    @9
    cV
    @6
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    @19
    dia2dimlem7.k
    wph
    cV
    cA
    wcel
    #
    @23
    wph
    @25
    @24
    dia2dimlem7.v
    simpld
    cA
    @6
    cV
    cK
    @12
    dia2dimlem7.a
    atbase
    syl
    wph
    @25
    @24
    dia2dimlem7.v
    simprd
    @6
    cS
    cY
    cH
    cI
    cK
    c.le
    cW
    cV
    @12
    dia2dimlem7.l
    dia2dimlem7.h
    dia2dimlem7.y
    dia2dimlem7.i
    dia2dimlem7.s
    dialss
    syl12anc
    c.po
    cS
    @0
    @1
    cY
    dia2dimlem7.s
    dia2dimlem7.pl
    lsmcl
    syl3anc
    cS
    @2
    cY
    @13
    @14
    dia2dimlem7.s
    lss0cl
    syl2anc
    eqeltrrd
    @7
    @2
    cF
    eleq1a
    syl
    sylbird
    imp
    wph
    @4
    cP
    wne
    #
    wa
    cA
    cP
    c.po
    cQ
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
    dia2dimlem7.l
    dia2dimlem7.j
    dia2dimlem7.m
    dia2dimlem7.a
    dia2dimlem7.h
    dia2dimlem7.t
    dia2dimlem7.r
    dia2dimlem7.y
    dia2dimlem7.s
    dia2dimlem7.pl
    dia2dimlem7.n
    dia2dimlem7.i
    dia2dimlem7.q
    wph
    @9
    @26
    dia2dimlem7.k
    adantr
    wph
    @22
    @21
    wa
    @26
    dia2dimlem7.u
    adantr
    wph
    @25
    @24
    wa
    @26
    dia2dimlem7.v
    adantr
    wph
    @11
    @26
    dia2dimlem7.p
    adantr
    wph
    @10
    @26
    dia2dimlem7.f
    anim1i
    wph
    cF
    cR
    cfv
    #
    cU
    cV
    c.or
    co
    c.le
    wbr
    @26
    dia2dimlem7.rf
    adantr
    wph
    cU
    cV
    wne
    @26
    dia2dimlem7.uv
    adantr
    wph
    @27
    cU
    wne
    @26
    dia2dimlem7.ru
    adantr
    wph
    @27
    cV
    wne
    @26
    dia2dimlem7.rv
    adantr
    dia2dimlem6
    pm2.61dane
end
