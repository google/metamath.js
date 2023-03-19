include "csn.mm"
include "cfv.mm"
include "co.mm"
include "clss.mm"
include "wcel.mm"
include "cv.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcl2.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lssel.mm"

theorem mapdpglem2a
  let wph: wff ph
  let vt: setvar t
  let cC: class C
  let c.po: class .(+)
  let cU: class U
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdpglem.h: |- H = ( LHyp ` K )
  assume mapdpglem.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdpglem.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdpglem.v: |- V = ( Base ` U )
  assume mapdpglem.s: |- .- = ( -g ` U )
  assume mapdpglem.n: |- N = ( LSpan ` U )
  assume mapdpglem.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdpglem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdpglem.x: |- ( ph -> X e. V )
  assume mapdpglem.y: |- ( ph -> Y e. V )
  assume mapdpglem1.p: |- .(+) = ( LSSum ` C )
  assume mapdpglem2.j: |- J = ( LSpan ` C )
  assume mapdpglem3.f: |- F = ( Base ` C )
  assume mapdpglem3.te: |- ( ph -> t e. ( ( M ` ( N ` { X } ) ) .(+) ( M ` ( N ` { Y } ) ) ) )

  disjoint .- t
  disjoint C t
  disjoint J t
  disjoint M t
  disjoint N t
  disjoint X t
  disjoint Y t
  assert |- ( ph -> t e. F )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    c.po
    co
    #
    cC
    clss
    cfv
    #
    wcel
    #
    vt
    cv
    #
    @4
    wcel
    @7
    cF
    wcel
    wph
    cC
    clmod
    wcel
    @1
    @5
    wcel
    @3
    @5
    wcel
    @6
    wph
    cC
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.c
    mapdpglem.k
    lcdlmod
    wph
    cC
    @0
    cU
    clss
    cfv
    #
    @5
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @8
    eqid
    #
    mapdpglem.c
    @5
    eqid
    #
    mapdpglem.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    @0
    @8
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem.k
    dvhlmod
    #
    mapdpglem.x
    @8
    cN
    cV
    cU
    cX
    mapdpglem.v
    @9
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    wph
    cC
    @2
    @8
    @5
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @9
    mapdpglem.c
    @10
    mapdpglem.k
    wph
    @11
    cY
    cV
    wcel
    @2
    @8
    wcel
    @12
    mapdpglem.y
    @8
    cN
    cV
    cU
    cY
    mapdpglem.v
    @9
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    c.po
    @5
    @1
    @3
    cC
    @10
    mapdpglem1.p
    lsmcl
    syl3anc
    mapdpglem3.te
    @5
    @4
    cF
    cC
    @7
    mapdpglem3.f
    @10
    lssel
    syl2anc
end
