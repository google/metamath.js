include "cv.mm"
include "wne.mm"
include "crn.mm"
include "wcel.mm"
include "dvh1dim.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "hgmaprnlem4N.mm"
include "sylan2br.mm"
include "rexlimddv.mm"

theorem hgmaprnlem5N
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vt: setvar t
  assume hgmaprnlem1.h: |- H = ( LHyp ` K )
  assume hgmaprnlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmaprnlem1.v: |- V = ( Base ` U )
  assume hgmaprnlem1.r: |- R = ( Scalar ` U )
  assume hgmaprnlem1.b: |- B = ( Base ` R )
  assume hgmaprnlem1.t: |- .x. = ( .s ` U )
  assume hgmaprnlem1.o: |- .0. = ( 0g ` U )
  assume hgmaprnlem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmaprnlem1.d: |- D = ( Base ` C )
  assume hgmaprnlem1.p: |- P = ( Scalar ` C )
  assume hgmaprnlem1.a: |- A = ( Base ` P )
  assume hgmaprnlem1.e: |- .xb = ( .s ` C )
  assume hgmaprnlem1.q: |- Q = ( 0g ` C )
  assume hgmaprnlem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hgmaprnlem1.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmaprnlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmaprnlem1.z: |- ( ph -> z e. A )


  assert |- ( ph -> z e. ran G )

  proof
    wph
    vt
    cv
    #
    c.0
    wne
    #
    vz
    cv
    #
    cG
    crn
    wcel
    #
    vt
    cV
    wph
    vt
    cU
    cH
    cK
    cV
    cW
    c.0
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.o
    hgmaprnlem1.k
    dvh1dim
    @0
    cV
    wcel
    @1
    wa
    wph
    @0
    cV
    c.0
    csn
    cdif
    wcel
    #
    @3
    @0
    cV
    c.0
    eldifsn
    wph
    @4
    wa
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    c.xb
    c.x
    cU
    cG
    cH
    cK
    cV
    cW
    c.0
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.t
    hgmaprnlem1.o
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.e
    hgmaprnlem1.q
    hgmaprnlem1.s
    hgmaprnlem1.g
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @4
    hgmaprnlem1.k
    adantr
    wph
    @2
    cA
    wcel
    @4
    hgmaprnlem1.z
    adantr
    wph
    @4
    simpr
    hgmaprnlem4N
    sylan2br
    rexlimddv
end
