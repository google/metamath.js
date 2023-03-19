include "cv.mm"
include "cop.mm"
include "cuni.mm"
include "wcel.mm"
include "w3a.mm"
include "biid.mm"
include "bnj1379.mm"

theorem bnj1383
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bnj1383.1: |- ( ph <-> A. f e. A Fun f )
  assume bnj1383.2: |- D = ( dom f i^i dom g )
  assume bnj1383.3: |- ( ps <-> ( ph /\ A. f e. A A. g e. A ( f |` D ) = ( g |` D ) ) )

  disjoint A f
  disjoint A g
  disjoint f g
  disjoint g ph
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D x
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( ps -> Fun U. A )

  proof
    wph
    wps
    wps
    vx
    cv
    #
    vy
    cv
    cop
    #
    cA
    cuni
    #
    wcel
    @0
    vz
    cv
    cop
    #
    @2
    wcel
    w3a
    #
    @4
    vf
    cv
    #
    cA
    wcel
    @1
    @5
    wcel
    w3a
    #
    @6
    vg
    cv
    #
    cA
    wcel
    @3
    @7
    wcel
    w3a
    #
    vx
    vy
    vz
    cA
    cD
    vf
    vg
    bnj1383.1
    bnj1383.2
    bnj1383.3
    @4
    biid
    @6
    biid
    @8
    biid
    bnj1379
end
