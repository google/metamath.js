include "dvhlmod.mm"
include "lspsnsubn0.mm"

theorem mapdpglem4N
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
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
  let vg: setvar g
  let vw: setvar w
  let vz: setvar z
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
  assume mapdpglem3.a: |- A = ( Scalar ` U )
  assume mapdpglem3.b: |- B = ( Base ` A )
  assume mapdpglem3.t: |- .x. = ( .s ` C )
  assume mapdpglem3.r: |- R = ( -g ` C )
  assume mapdpglem3.g: |- ( ph -> G e. F )
  assume mapdpglem3.e: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { G } ) )
  assume mapdpglem4.q: |- Q = ( 0g ` U )
  assume mapdpglem.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )

  disjoint .- t
  disjoint C t
  disjoint J t
  disjoint M t
  disjoint N t
  disjoint X t
  disjoint Y t
  disjoint g w
  disjoint B g
  disjoint B w
  disjoint g z
  disjoint C g
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint F g
  disjoint G g
  disjoint G w
  disjoint G z
  disjoint J g
  disjoint J w
  disjoint J z
  disjoint M g
  disjoint M w
  disjoint M z
  disjoint N g
  disjoint N w
  disjoint N z
  disjoint R g
  disjoint R w
  disjoint R z
  disjoint .x. g
  disjoint .x. w
  disjoint .x. z
  disjoint Y g
  disjoint Y w
  disjoint Y z
  disjoint g t
  disjoint t w
  disjoint t z
  assert |- ( ph -> ( X .- Y ) =/= Q )

  proof
    wph
    c.mi
    cN
    cV
    cU
    cX
    cY
    cQ
    mapdpglem.v
    mapdpglem4.q
    mapdpglem.s
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
    mapdpglem.ne
    lspsnsubn0
end
