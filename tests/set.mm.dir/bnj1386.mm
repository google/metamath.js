include "cv.mm"
include "cdm.mm"
include "cin.mm"
include "wfun.mm"
include "wral.mm"
include "cres.mm"
include "wceq.mm"
include "wa.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1385.mm"

theorem bnj1386
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assume bnj1386.1: |- ( ph <-> A. f e. A Fun f )
  assume bnj1386.2: |- D = ( dom f i^i dom g )
  assume bnj1386.3: |- ( ps <-> ( ph /\ A. f e. A A. g e. A ( f |` D ) = ( g |` D ) ) )
  assume bnj1386.4: |- ( x e. A -> A. f x e. A )

  disjoint A g
  disjoint A x
  disjoint g x
  disjoint f g
  disjoint f x
  disjoint A h
  disjoint g h
  disjoint h x
  disjoint D h
  disjoint f h
  assert |- ( ps -> Fun U. A )

  proof
    wph
    wps
    vx
    cA
    cD
    vf
    vg
    vh
    vh
    cv
    #
    cdm
    vg
    cv
    #
    cdm
    cin
    #
    @0
    wfun
    vh
    cA
    wral
    #
    @3
    @0
    @2
    cres
    @1
    @2
    cres
    wceq
    vg
    cA
    wral
    vh
    cA
    wral
    wa
    #
    bnj1386.1
    bnj1386.2
    bnj1386.3
    bnj1386.4
    @3
    biid
    @2
    eqid
    @4
    biid
    bnj1385
end
