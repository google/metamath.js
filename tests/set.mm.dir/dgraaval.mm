include "cv.mm"
include "cdgr.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "caa.mm"
include "cdgraa.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "df-dgraa.mm"
include "ltso.mm"
include "infex.mm"
include "fvmpt.mm"

theorem dgraaval
  let cA: class A
  let vp: setvar p
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cP: class P

  disjoint A d
  disjoint A p
  disjoint d p
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint P d
  disjoint P p
  disjoint P a
  disjoint P b
  disjoint P c
  assert |- ( A e. AA -> ( degAA ` A ) = inf ( { d e. NN | E. p e. ( ( Poly ` QQ ) \ { 0p } ) ( ( deg ` p ) = d /\ ( p ` A ) = 0 ) } , RR , < ) )

  proof
    va
    cA
    vp
    cv
    #
    cdgr
    cfv
    vd
    cv
    wceq
    #
    va
    cv
    #
    @0
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vp
    cq
    cply
    cfv
    c0p
    csn
    cdif
    #
    wrex
    #
    vd
    cn
    crab
    #
    cr
    clt
    cinf
    @1
    cA
    @0
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vp
    @6
    wrex
    #
    vd
    cn
    crab
    #
    cr
    clt
    cinf
    caa
    cdgraa
    @2
    cA
    wceq
    #
    cr
    @8
    @13
    clt
    @14
    @7
    @12
    vd
    cn
    @14
    @5
    @11
    vp
    @6
    @14
    @4
    @10
    @1
    @14
    @3
    @9
    cc0
    @2
    cA
    @0
    fveq2
    eqeq1d
    anbi2d
    rexbidv
    rabbidv
    infeq1d
    va
    vp
    vd
    df-dgraa
    cr
    @13
    clt
    ltso
    infex
    fvmpt
end
