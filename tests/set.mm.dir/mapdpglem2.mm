include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cbs.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "mapdspex.mm"
include "wa.mm"
include "lcdlmod.mm"
include "lspsnid.mm"
include "sylan.mm"
include "adantrr.mm"
include "simprr.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "mapdpglem1.mm"
include "sseld.mm"
include "anim1d.mm"

theorem mapdpglem2
  let wph: wff ph
  let vt: setvar t
  let cC: class C
  let c.po: class .(+)
  let cU: class U
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

  disjoint ph t
  disjoint .- t
  disjoint C t
  disjoint J t
  disjoint M t
  disjoint N t
  disjoint X t
  disjoint Y t
  assert |- ( ph -> E. t e. ( ( M ` ( N ` { X } ) ) .(+) ( M ` ( N ` { Y } ) ) ) ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { t } ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    csn
    cN
    cfv
    cM
    cfv
    #
    vt
    cv
    #
    csn
    cJ
    cfv
    #
    wceq
    #
    vt
    @1
    wrex
    #
    @4
    vt
    cX
    csn
    cN
    cfv
    cM
    cfv
    cY
    csn
    cN
    cfv
    cM
    cfv
    c.po
    co
    #
    wrex
    wph
    @4
    vt
    cC
    cbs
    cfv
    #
    wrex
    @5
    wph
    @7
    cC
    cU
    vt
    cH
    cJ
    cK
    cM
    cN
    cV
    cW
    @0
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    mapdpglem.v
    mapdpglem.n
    mapdpglem.c
    @7
    eqid
    #
    mapdpglem2.j
    mapdpglem.k
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    @0
    cV
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
    mapdpglem.x
    mapdpglem.y
    c.mi
    cV
    cU
    cX
    cY
    mapdpglem.v
    mapdpglem.s
    lmodvsubcl
    syl3anc
    mapdspex
    wph
    @4
    @4
    vt
    @7
    @1
    wph
    @2
    @7
    wcel
    #
    @4
    wa
    #
    @2
    @1
    wcel
    #
    @4
    wa
    wph
    @10
    wa
    #
    @11
    @4
    @12
    @2
    @3
    @1
    wph
    @9
    @2
    @3
    wcel
    #
    @4
    wph
    cC
    clmod
    wcel
    @9
    @13
    wph
    cC
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.c
    mapdpglem.k
    lcdlmod
    cJ
    @7
    cC
    @2
    @8
    mapdpglem2.j
    lspsnid
    sylan
    adantrr
    wph
    @9
    @4
    simprr
    #
    eleqtrrd
    @14
    jca
    ex
    reximdv2
    mpd
    wph
    @4
    @4
    vt
    @1
    @6
    wph
    @11
    @2
    @6
    wcel
    @4
    wph
    @1
    @6
    @2
    wph
    cC
    c.po
    cU
    cH
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    mapdpglem.v
    mapdpglem.s
    mapdpglem.n
    mapdpglem.c
    mapdpglem.k
    mapdpglem.x
    mapdpglem.y
    mapdpglem1.p
    mapdpglem1
    sseld
    anim1d
    reximdv2
    mpd
end
