include "co.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "oveq2.mm"
include "adantl.mm"
include "chlt.mm"
include "wcel.mm"
include "simpld.mm"
include "wbr.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "csubg.mm"
include "clmod.mm"
include "clvec.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "3syl.mm"
include "cbs.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simprd.mm"
include "dialss.mm"
include "syl12anc.mm"
include "lsssubg.mm"
include "lsmidm.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sylan9req.mm"
include "sseqtrd.mm"
include "wne.mm"
include "simpr.mm"
include "dia2dimlem12.mm"
include "pm2.61dane.mm"

theorem dia2dimlem13
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
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
  let vf: setvar f
  assume dia2dimlem12.l: |- .<_ = ( le ` K )
  assume dia2dimlem12.j: |- .\/ = ( join ` K )
  assume dia2dimlem12.m: |- ./\ = ( meet ` K )
  assume dia2dimlem12.a: |- A = ( Atoms ` K )
  assume dia2dimlem12.h: |- H = ( LHyp ` K )
  assume dia2dimlem12.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia2dimlem12.r: |- R = ( ( trL ` K ) ` W )
  assume dia2dimlem12.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dimlem12.s: |- S = ( LSubSp ` Y )
  assume dia2dimlem12.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dimlem12.n: |- N = ( LSpan ` Y )
  assume dia2dimlem12.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dimlem12.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dimlem12.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dimlem12.v: |- ( ph -> ( V e. A /\ V .<_ W ) )


  assert |- ( ph -> ( I ` ( U .\/ V ) ) C_ ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cU
    cV
    c.or
    co
    #
    cI
    cfv
    #
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
    wss
    cU
    cV
    wph
    cU
    cV
    wceq
    #
    wa
    #
    @1
    @2
    @4
    @6
    @1
    @2
    @2
    @6
    @0
    cU
    cI
    @6
    cU
    cU
    c.or
    co
    #
    @0
    cU
    @5
    @7
    @0
    wceq
    wph
    cU
    cV
    cU
    c.or
    oveq2
    adantl
    wph
    @7
    cU
    wceq
    #
    @5
    wph
    cK
    chlt
    wcel
    #
    cU
    cA
    wcel
    #
    @8
    wph
    @9
    cW
    cH
    wcel
    #
    dia2dimlem12.k
    simpld
    wph
    @10
    cU
    cW
    c.le
    wbr
    #
    dia2dimlem12.u
    simpld
    #
    cA
    c.or
    cK
    cU
    dia2dimlem12.j
    dia2dimlem12.a
    hlatjidm
    syl2anc
    adantr
    eqtr3d
    fveq2d
    @2
    ssid
    syl6eqss
    wph
    @5
    @2
    @2
    @2
    c.po
    co
    #
    @4
    wph
    @2
    cY
    csubg
    cfv
    wcel
    #
    @14
    @2
    wceq
    wph
    cY
    clmod
    wcel
    #
    @2
    cS
    wcel
    #
    @15
    wph
    @9
    @11
    wa
    #
    cY
    clvec
    wcel
    @16
    dia2dimlem12.k
    cY
    cH
    cK
    cW
    dia2dimlem12.h
    dia2dimlem12.y
    dvalvec
    cY
    lveclmod
    3syl
    wph
    @18
    cU
    cK
    cbs
    cfv
    #
    wcel
    #
    @12
    @17
    dia2dimlem12.k
    wph
    @10
    @20
    @13
    cA
    @19
    cU
    cK
    @19
    eqid
    #
    dia2dimlem12.a
    atbase
    syl
    wph
    @10
    @12
    dia2dimlem12.u
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
    @21
    dia2dimlem12.l
    dia2dimlem12.h
    dia2dimlem12.y
    dia2dimlem12.i
    dia2dimlem12.s
    dialss
    syl12anc
    cS
    @2
    cY
    dia2dimlem12.s
    lsssubg
    syl2anc
    c.po
    @2
    cY
    dia2dimlem12.pl
    lsmidm
    syl
    @5
    @2
    @3
    @2
    c.po
    cU
    cV
    cI
    fveq2
    oveq2d
    sylan9req
    sseqtrd
    wph
    cU
    cV
    wne
    #
    wa
    cA
    c.po
    cR
    cS
    cT
    cU
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
    dia2dimlem12.l
    dia2dimlem12.j
    dia2dimlem12.m
    dia2dimlem12.a
    dia2dimlem12.h
    dia2dimlem12.t
    dia2dimlem12.r
    dia2dimlem12.y
    dia2dimlem12.s
    dia2dimlem12.pl
    dia2dimlem12.n
    dia2dimlem12.i
    wph
    @18
    @22
    dia2dimlem12.k
    adantr
    wph
    @10
    @12
    wa
    @22
    dia2dimlem12.u
    adantr
    wph
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    wa
    @22
    dia2dimlem12.v
    adantr
    wph
    @22
    simpr
    dia2dimlem12
    pm2.61dane
end
