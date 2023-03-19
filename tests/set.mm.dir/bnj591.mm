include "cv.mm"
include "wsbc.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "sbcbii.mm"
include "vex.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "sbcie.mm"
include "bitri.mm"

theorem bnj591
  let wch: wff ch
  let wth: wff th
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let bnjwchm: wff ch'
  assume bnj591.1: |- ( th <-> ( ( n e. D /\ ch /\ ch' ) -> ( f ` j ) = ( g ` j ) ) )

  disjoint D j
  disjoint ch j
  disjoint ch' j
  disjoint f j
  disjoint g j
  disjoint j k
  disjoint j n
  assert |- ( [. k / j ]. th <-> ( ( n e. D /\ ch /\ ch' ) -> ( f ` k ) = ( g ` k ) ) )

  proof
    wth
    vj
    vk
    cv
    #
    wsbc
    vn
    cv
    cD
    wcel
    wch
    bnjwchm
    w3a
    #
    vj
    cv
    #
    vf
    cv
    #
    cfv
    #
    @2
    vg
    cv
    #
    cfv
    #
    wceq
    #
    wi
    #
    vj
    @0
    wsbc
    @1
    @0
    @3
    cfv
    #
    @0
    @5
    cfv
    #
    wceq
    #
    wi
    #
    wth
    @8
    vj
    @0
    bnj591.1
    sbcbii
    @8
    @12
    vj
    @0
    vk
    vex
    vj
    vk
    weq
    #
    @7
    @11
    @1
    @13
    @4
    @9
    @6
    @10
    @2
    @0
    @3
    fveq2
    @2
    @0
    @5
    fveq2
    eqeq12d
    imbi2d
    sbcie
    bitri
end
