include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "chlt.mm"
include "wa.mm"
include "cbs.mm"
include "wbr.mm"
include "wss.mm"
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
include "diass.mm"
include "syl12anc.mm"
include "sseld.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wne.mm"
include "simp2.mm"
include "dia2dimlem11.mm"
include "3exp.mm"
include "mpdd.mm"
include "ssrdv.mm"

theorem dia2dimlem12
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
  assume dia2dimlem12.uv: |- ( ph -> U =/= V )


  assert |- ( ph -> ( I ` ( U .\/ V ) ) C_ ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    vf
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
    cV
    cI
    cfv
    c.po
    co
    #
    wph
    vf
    cv
    #
    @1
    wcel
    #
    @3
    cT
    wcel
    #
    @3
    @2
    wcel
    #
    wph
    @1
    cT
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
    @0
    cK
    cbs
    cfv
    #
    wcel
    #
    @0
    cW
    c.le
    wbr
    #
    @1
    cT
    wss
    dia2dimlem12.k
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
    @11
    wph
    @7
    @8
    dia2dimlem12.k
    simpld
    #
    wph
    @13
    cU
    cW
    c.le
    wbr
    #
    dia2dimlem12.u
    simpld
    #
    wph
    @14
    cV
    cW
    c.le
    wbr
    #
    dia2dimlem12.v
    simpld
    #
    cA
    @10
    c.or
    cK
    cU
    cV
    @10
    eqid
    #
    dia2dimlem12.j
    dia2dimlem12.a
    hlatjcl
    syl3anc
    wph
    @16
    @18
    @12
    wph
    @13
    @16
    dia2dimlem12.u
    simprd
    wph
    @14
    @18
    dia2dimlem12.v
    simprd
    wph
    cK
    clat
    wcel
    #
    cU
    @10
    wcel
    #
    cV
    @10
    wcel
    #
    cW
    @10
    wcel
    #
    @16
    @18
    wa
    @12
    wb
    wph
    @7
    @21
    @15
    cK
    hllat
    syl
    wph
    @13
    @22
    @17
    cA
    @10
    cU
    cK
    @20
    dia2dimlem12.a
    atbase
    syl
    wph
    @14
    @23
    @19
    cA
    @10
    cV
    cK
    @20
    dia2dimlem12.a
    atbase
    syl
    wph
    @8
    @24
    wph
    @7
    @8
    dia2dimlem12.k
    simprd
    @10
    cH
    cK
    cW
    @20
    dia2dimlem12.h
    lhpbase
    syl
    @10
    c.or
    cK
    c.le
    cU
    cV
    cW
    @20
    dia2dimlem12.l
    dia2dimlem12.j
    latjle12
    syl13anc
    mpbi2and
    @10
    cT
    cH
    cI
    cK
    c.le
    chlt
    cW
    @0
    @20
    dia2dimlem12.l
    dia2dimlem12.h
    dia2dimlem12.t
    dia2dimlem12.i
    diass
    syl12anc
    sseld
    wph
    @4
    @5
    @6
    wph
    @4
    @5
    w3a
    cA
    c.po
    cR
    cS
    cT
    cU
    @3
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
    @4
    @9
    @5
    dia2dimlem12.k
    3ad2ant1
    wph
    @4
    @13
    @16
    wa
    @5
    dia2dimlem12.u
    3ad2ant1
    wph
    @4
    @14
    @18
    wa
    @5
    dia2dimlem12.v
    3ad2ant1
    wph
    @4
    @5
    simp3
    wph
    @4
    cU
    cV
    wne
    @5
    dia2dimlem12.uv
    3ad2ant1
    wph
    @4
    @5
    simp2
    dia2dimlem11
    3exp
    mpdd
    ssrdv
end
